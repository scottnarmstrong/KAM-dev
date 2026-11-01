# W-w7a: slice review 1

Reviewer: sol-review-W-w7a. Verdict: **FAIL**.

Read w7-measure.tex L1-L459 in full, including all excluded prose/source notes. Reconstructed the four source fields and checked the W0 normal frequencies, A/B coefficients and nondegeneracy suppliers. Bare lambda and phase phi introduce no lam/sineMode edges. The Xzones#consts split is faithful as a definition of minima, not a proof that they are positive. The additional base split below repairs the remaining dependency on (C2); positivity stays in X-A3.

Source-only topology review. PASS does not assert mathematical proof completion or Lean closure. No implementation Lean was read, and no Lean, Lake, build, source lint or state-changing git command was run.

The eleven corpus hashes were checked with sha256sum -c docs/graph/W/CORPUS.sha256: all OK. The permitted read-only slice checker returned zero problems for this packet.

Packet snapshot SHA-256: nodes 95223d9800b3e58838ede14e39bea462fef71048deaab03f4ab4ac7b8b3de0f4; coverage 014853266967dd2621a9e7ea89867e85c9d68397ed4524f98662714cb5eee5af.

## Node verdicts

| Node | Verdict | Evidence / reason |
| --- | --- | --- |
| bpW:w7:ext-tonelli | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:ext-tonelli@L47-L51 |
| bpW:w7:ext-diam | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:ext-diam@L52-L54 |
| bpW:w7:ext-linear | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:ext-linear@L55-L57 |
| bpW:w7:ext-borel | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:ext-borel@L58-L65 |
| bpW:w7:ext-zeta | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:ext-zeta@L66-L68 |
| bpW:w7:ext-ball | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:ext-ball@L69-L71 |
| bpW:w7:ext-ennreal | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:ext-ennreal@L72-L76 |
| bpW:w7:indexdef | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:indexdef@L82-L98 |
| bpW:w7:omega0 | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:omega0@L127-L131 |
| bpW:w7:freqcoords | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:freqcoords@L135-L150; blueprint-W/parts/w7-measure.tex#bpW:w7:freqcoords@L151-L168 |
| stepW:w7:inverse | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:inverse@L152-L157; blueprint-W/parts/w7-measure.tex#stepW:w7:inverse@L152-L157 |
| stepW:w7:norms | FAIL | The row-sum computation consumes the previously computed inverse and the corrected A; both direct edges are missing. |
| stepW:w7:Omegazeta | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:Omegazeta@L163-L165; blueprint-W/parts/w7-measure.tex#stepW:w7:Omegazeta@L163-L165 |
| stepW:w7:measure-affine | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:measure-affine@L166-L167; blueprint-W/parts/w7-measure.tex#stepW:w7:measure-affine@L166-L167 |
| bpW:w7:unpert-bounds | FAIL | The freqcoords EDGE points at the lemma heading L172; zeta = omega^0(xi) and s are introduced from L173. |
| stepW:w7:ssize | FAIL | The strict reciprocal bound uses lambda_1 > 1 and lambda_2 > 2; the lambda-facts edge is missing. |
| stepW:w7:plus | FAIL | The lambda-facts EDGE points at L188, whereas lambda_j >= j is consumed at L187. |
| stepW:w7:minus | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:minus@L190-L194; blueprint-W/parts/w7-measure.tex#stepW:w7:minus@L190-L194 |
| stepW:w7:kappa | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:kappa@L195-L200; blueprint-W/parts/w7-measure.tex#stepW:w7:kappa@L195-L200 |
| stepW:w7:liplOmega | FAIL | The affine Omega^0 and s formula is consumed from frequency coordinates, without an edge. |
| bpW:w7:constdef | FAIL | C1-C2 must be available independently before X is defined; the current full constant block cannot supply the missing Xdef edge without a cycle. |
| bpW:w7:zones | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:zones@L255-L264 |
| bpW:w7:family | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:family@L266-L280 |
| bpW:w7:slab | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:slab@L317-L322; blueprint-W/parts/w7-measure.tex#bpW:w7:slab@L323-L334 |
| stepW:w7:slab-borel | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:slab-borel@L324-L325; blueprint-W/parts/w7-measure.tex#stepW:w7:slab-borel@L324-L325 |
| stepW:w7:slab-line | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:slab-line@L326-L329; blueprint-W/parts/w7-measure.tex#stepW:w7:slab-line@L326-L329 |
| stepW:w7:slab-int | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:slab-int@L330-L333; blueprint-W/parts/w7-measure.tex#stepW:w7:slab-int@L330-L333 |
| bpW:w7:sep | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:sep@L345-L348; blueprint-W/parts/w7-measure.tex#bpW:w7:sep@L349-L356 |
| stepW:w7:sep-drift | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:sep-drift@L350-L352; blueprint-W/parts/w7-measure.tex#stepW:w7:sep-drift@L350-L352 |
| stepW:w7:sep-concl | FAIL | The emptiness proof directly consumes the zone definitions, the weight inequality and (C4). |
| bpW:w7:largek | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:largek@L359-L363; blueprint-W/parts/w7-measure.tex#bpW:w7:largek@L364-L371 |
| stepW:w7:largek-tan | FAIL | The bound by W uses its definition and alpha's smallness, with no constant-definition edge. |
| stepW:w7:largek-cmp | FAIL | The proof context drops the nonempty-zone antecedent of largek. |
| bpW:w7:zone | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:zone@L374-L380; blueprint-W/parts/w7-measure.tex#bpW:w7:zone@L381-L394 |
| stepW:w7:zone-lower | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:zone-lower@L382-L386; blueprint-W/parts/w7-measure.tex#stepW:w7:zone-lower@L382-L386 |
| stepW:w7:zone-slab | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:zone-slab@L387-L389; blueprint-W/parts/w7-measure.tex#stepW:w7:zone-slab@L387-L389 |
| stepW:w7:zone-psi | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:zone-psi@L390-L393; blueprint-W/parts/w7-measure.tex#stepW:w7:zone-psi@L390-L393 |
| bpW:w7:Xdef | FAIL | X uses K_*, vartheta and j_* from (C2), but its only edge is to indexdef. Use the independent base definition to avoid a cycle. |
| bpW:w7:dichotomy | FAIL | The statement uses the fixed frequency-pair data but has no basic-data edge. |
| stepW:w7:Xfinite | FAIL | The finiteness argument consumes the definition and cutoffs of X, with no edge to Xdef. |
| stepW:w7:dich-large | FAIL | The proof context omits the nonempty-zone antecedent of dichotomy. |
| stepW:w7:dich-small | FAIL | The argument consumes X's definition and the largek conclusion from the preceding step. |
| bpW:w7:Xzones | FAIL | Exceptional zones use the frequency pair, domain and phi_kl fixed by basic#data but have no direct edge to that data definition. |
| stepW:w7:X-A3 | FAIL | Strict positivity of the minima consumes finiteness of X and their definitions; neither is a direct dependency. |
| stepW:w7:X-const | FAIL | The bounds ¦k¦ < K_* and <l> < K_*/vartheta use X's definition directly. |
| stepW:w7:X-slope | FAIL | Slicing requires sigma_X > 0, established by X-A3, and the estimates use X's cutoffs; both edges are missing. |
| bpW:w7:count | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:count@L449-L452; blueprint-W/parts/w7-measure.tex#bpW:w7:count@L453-L457 |
| bpW:w7#data | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7@L33-L41 |
| bpW:w7:basic#data | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:basic@L339-L343 |
| bpW:w7:Xzones#consts | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:Xzones@L422-L426 |
| bpW:w7:constdef#base | FAIL | Missing node; source re-read: blueprint-W/parts/w7-measure.tex#bpW:w7:constdef@L214-L217. Complete addition below. |

## Coverage verdicts

| Coverage item | Verdict | Evidence / reason |
| --- | --- | --- |
| bpW:w7:ext-tonelli | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:ext-tonelli@L47-L51 |
| bpW:w7:ext-diam | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:ext-diam@L52-L54 |
| bpW:w7:ext-linear | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:ext-linear@L55-L57 |
| bpW:w7:ext-borel | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:ext-borel@L58-L65 |
| bpW:w7:ext-zeta | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:ext-zeta@L66-L68 |
| bpW:w7:ext-ball | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:ext-ball@L69-L71 |
| bpW:w7:ext-ennreal | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:ext-ennreal@L72-L76 |
| bpW:w7:indexdef | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:indexdef@L82-L98 |
| bpW:w7:reindex | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:reindex@L103-L119 |
| bpW:w7:omega0 | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:omega0@L127-L131 |
| bpW:w7:freqcoords | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:freqcoords@L135-L150 |
| stepW:w7:inverse | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:inverse@L152-L157 |
| stepW:w7:norms | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:norms@L158-L162 |
| stepW:w7:Omegazeta | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:Omegazeta@L163-L165 |
| stepW:w7:measure-affine | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:measure-affine@L166-L167 |
| bpW:w7:unpert-bounds | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:unpert-bounds@L172-L181 |
| stepW:w7:ssize | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:ssize@L183-L185 |
| stepW:w7:plus | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:plus@L186-L189 |
| stepW:w7:minus | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:minus@L190-L194 |
| stepW:w7:kappa | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:kappa@L195-L200 |
| stepW:w7:liplOmega | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:liplOmega@L201-L203 |
| bpW:w7:constdef | FAIL | The preliminary definition must also be mapped to its cycle-free base node. |
| bpW:w7:choices | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:choices@L235-L251 |
| bpW:w7:zones | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:zones@L255-L264 |
| bpW:w7:family | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:family@L266-L280 |
| bpW:w7:w6-needs | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:w6-needs@L286-L313 |
| bpW:w7:slab | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:slab@L317-L322 |
| stepW:w7:slab-borel | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:slab-borel@L324-L325 |
| stepW:w7:slab-line | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:slab-line@L326-L329 |
| stepW:w7:slab-int | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:slab-int@L330-L333 |
| bpW:w7:sep | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:sep@L345-L348 |
| stepW:w7:sep-drift | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:sep-drift@L350-L352 |
| stepW:w7:sep-concl | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:sep-concl@L353-L355 |
| bpW:w7:largek | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:largek@L359-L363 |
| stepW:w7:largek-tan | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:largek-tan@L365-L367 |
| stepW:w7:largek-cmp | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:largek-cmp@L368-L370 |
| bpW:w7:zone | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:zone@L374-L380 |
| stepW:w7:zone-lower | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:zone-lower@L382-L386 |
| stepW:w7:zone-slab | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:zone-slab@L387-L389 |
| stepW:w7:zone-psi | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:zone-psi@L390-L393 |
| bpW:w7:Xdef | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:Xdef@L398-L401 |
| bpW:w7:dichotomy | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:dichotomy@L403-L406 |
| stepW:w7:Xfinite | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:Xfinite@L408-L410 |
| stepW:w7:dich-large | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:dich-large@L411-L413 |
| stepW:w7:dich-small | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:dich-small@L414-L416 |
| bpW:w7:Xzones | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:Xzones@L421-L429 |
| stepW:w7:X-A3 | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:X-A3@L431-L435 |
| stepW:w7:X-const | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:X-const@L436-L438 |
| stepW:w7:X-slope | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:X-slope@L439-L443 |
| bpW:w7:count | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:count@L449-L452 |
| heading:bpW:w7 | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7@L1-L1 |
| heading:bpW:w7:ext | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:ext@L43-L43 |
| heading:bpW:w7:indices | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:indices@L80-L80 |
| heading:bpW:w7:unpert | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:unpert@L122-L122 |
| heading:bpW:w7:constants | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:constants@L209-L209 |
| heading:bpW:w7:interface-sec | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:interface-sec@L253-L253 |
| heading:bpW:w7:basic | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:basic@L315-L315 |
| w7-measure:source-L99 | PASS | blueprint-W/parts/w7-measure.tex#source@L99-L99 |
| w7-measure:source-L120 | PASS | blueprint-W/parts/w7-measure.tex#source@L120-L120 |
| w7-measure:source-L132 | PASS | blueprint-W/parts/w7-measure.tex#source@L132-L132 |
| w7-measure:source-L169 | PASS | blueprint-W/parts/w7-measure.tex#source@L169-L169 |
| w7-measure:source-L205 | PASS | blueprint-W/parts/w7-measure.tex#source@L205-L205 |
| w7-measure:source-L232 | PASS | blueprint-W/parts/w7-measure.tex#source@L232-L232 |
| w7-measure:source-L281 | PASS | blueprint-W/parts/w7-measure.tex#source@L281-L281 |
| w7-measure:source-L335 | PASS | blueprint-W/parts/w7-measure.tex#source@L335-L335 |
| w7-measure:source-L357 | PASS | blueprint-W/parts/w7-measure.tex#source@L357-L357 |
| w7-measure:source-L372 | PASS | blueprint-W/parts/w7-measure.tex#source@L372-L372 |
| w7-measure:source-L395 | PASS | blueprint-W/parts/w7-measure.tex#source@L395-L395 |
| w7-measure:source-L418 | PASS | blueprint-W/parts/w7-measure.tex#source@L418-L418 |
| w7-measure:source-L445 | PASS | blueprint-W/parts/w7-measure.tex#source@L445-L445 |
| w7-measure:source-L458 | PASS | blueprint-W/parts/w7-measure.tex#source@L458-L458 |
| w7-measure:prose-L3-L8 | PASS | blueprint-W/parts/w7-measure.tex#prose@L3-L8 |
| w7-measure:prose-L10-L21 | PASS | blueprint-W/parts/w7-measure.tex#prose@L10-L21 |
| w7-measure:prose-L23-L31 | PASS | blueprint-W/parts/w7-measure.tex#prose@L23-L31 |
| w7-measure:prose-L33-L41 | PASS | blueprint-W/parts/w7-measure.tex#prose@L33-L41 |
| w7-measure:prose-L45-L46 | PASS | blueprint-W/parts/w7-measure.tex#prose@L45-L46 |
| w7-measure:prose-L77-L78 | PASS | blueprint-W/parts/w7-measure.tex#prose@L77-L78 |
| w7-measure:prose-L124-L125 | PASS | blueprint-W/parts/w7-measure.tex#prose@L124-L125 |
| w7-measure:prose-L339-L343 | PASS | blueprint-W/parts/w7-measure.tex#prose@L339-L343 |

all other coverage items PASS.

## Complete replacement fragments

These are proposals only. Existing packet records are unchanged. New and revised records remain PROPOSED for an independent delta reviewer.

```text
NODE: stepW:w7:norms
KIND: step
TITLE: Norms
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:norms@L158-L162
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:norms@L158-L162
CONTRACT_ID: stepW:w7:norms
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:freqcoords: W7 standing data (L33-L41): m > 0, lambda_j = sqrt(j^2+m), corrected A, B, max norms on R^2, Leb, ¦k¦ = ¦k_1¦ + ¦k_2¦
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:freqcoords (for Borel F subset R^2; xi, xi'); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: N_A < 3/5 and L_A
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#lambda-facts, bpW:w0:basis#lam, stepW:w7:inverse, bpW:w0n:AB
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w7-measure.tex#stepW:w7:norms@L160-L160 | lambda_1 > 1, lambda_2 > 2, lambda increasing
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w7-measure.tex#stepW:w7:norms@L160-L160 | lambda occurs directly here (frozen lam)
EDGE: stepW:w7:inverse | blueprint-W/parts/w7-measure.tex#stepW:w7:norms@L159-L162 | row sums of the displayed inverse computed in the preceding step
EDGE: bpW:w0n:AB | blueprint-W/parts/w7-measure.tex#stepW:w7:norms@L159-L159 | row sums of the corrected A
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w7:ssize
KIND: step
TITLE: Size of $s$
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:ssize@L183-L185
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:ssize@L183-L185
CONTRACT_ID: stepW:w7:ssize
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:unpert-bounds: W7 standing data (L33-L41): m > 0, lambda_j = sqrt(j^2+m), corrected A, B, max norms on R^2, Leb, ¦k¦ = ¦k_1¦ + ¦k_2¦; ¦xi¦_infty <= 1/2, zeta = omega^0(xi); beta_* = 1/(2 sqrt(9+m)), a_kappa = m/2 + 1
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:unpert-bounds (for such xi; l in Lambda; i > j >= 3); within the step: xi; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦s¦ <= 1 and ¦A xi¦ < 3/10
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:freqcoords, bpW:w0:basis#lam, bpW:w0:basis#lambda-facts
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w7-measure.tex#stepW:w7:ssize@L185-L185 | (ii), (iii)
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w7-measure.tex#stepW:w7:ssize@L184-L184 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w7-measure.tex#stepW:w7:ssize@L184-L184 | lambda_1 > 1 and lambda_2 > 2 give the reciprocal bound
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w7:liplOmega
KIND: step
TITLE: Lipschitz
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:liplOmega@L201-L203
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:liplOmega@L201-L203
CONTRACT_ID: stepW:w7:liplOmega
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:unpert-bounds: W7 standing data (L33-L41): m > 0, lambda_j = sqrt(j^2+m), corrected A, B, max norms on R^2, Leb, ¦k¦ = ¦k_1¦ + ¦k_2¦; ¦xi¦_infty <= 1/2, zeta = omega^0(xi); beta_* = 1/(2 sqrt(9+m)), a_kappa = m/2 + 1
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:unpert-bounds (for such xi; l in Lambda; i > j >= 3); within the step: zeta, zeta'; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iv) the Lipschitz bound
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#lam, bpW:w7:freqcoords
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w7-measure.tex#stepW:w7:liplOmega@L202-L202 | lambda occurs directly here (frozen lam)
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w7-measure.tex#stepW:w7:liplOmega@L202-L203 | the affine Omega^0 formula and s(zeta) from (iii)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: bpW:w7:constdef
KIND: definition
TITLE: W7 constants
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:constdef@L211-L231
PROOF_SOURCE: -
CONTRACT_ID: bpW:w7:constdef
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W7 standing data (L33-L41): m > 0, lambda_j = sqrt(j^2+m), corrected A, B, max norms on R^2, Leb, ¦k¦ = ¦k_1¦ + ¦k_2¦; m > 0
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: defines in order (C1) tau = 24, varpi = 1/2, beta = 1/4, w = 1/47; (C2) lambda_1, lambda_2, D_A, N_A, L_A, beta_*, a_kappa, W = lambda_2 + 1, vartheta = beta_*/W, c_Lambda = (4/7)(lambda_1 + lambda_2) + 1, K_* = 16 c_Lambda, j_* = (16 c_Lambda)^2; (C3) X, N_X, sigma_X, c_X; (C4) theta_0 and alpha_0; (C5) C_P, C_I, C_7 = L_A(C_P + C_I); (C6) per application Pi, alpha in (0,alpha_0], hat alpha = alpha^{44/47}, check alpha = alpha^{48/47}; every constant of (C1)-(C5) depends on m only
CONSTANT_SCOPE: (C1)-(C5) depend on m only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:freqcoords, bpW:w7:unpert-bounds, bpW:w7:Xdef, bpW:w7:Xzones#consts, bpW:w7:ext-zeta, bpW:w0:basis#lam, bpW:w7:constdef#base
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w7-measure.tex#bpW:w7:constdef@L215-L215 | D_A, N_A, L_A
EDGE: bpW:w7:unpert-bounds | blueprint-W/parts/w7-measure.tex#bpW:w7:constdef@L216-L216 | beta_*, a_kappa
EDGE: bpW:w7:Xdef | blueprint-W/parts/w7-measure.tex#bpW:w7:constdef@L218-L218 | X
EDGE: bpW:w7:Xzones#consts | blueprint-W/parts/w7-measure.tex#bpW:w7:constdef@L219-L219 | sigma_X, c_X (defined in the statement of Lemma bpW:w7:Xzones)
EDGE: bpW:w7:ext-zeta | blueprint-W/parts/w7-measure.tex#bpW:w7:constdef@L225-L225 | Z_3
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w7-measure.tex#bpW:w7:constdef@L215-L215 | lambda occurs directly here (frozen lam)
EDGE: bpW:w7:constdef#base | blueprint-W/parts/w7-measure.tex#bpW:w7:constdef@L214-L217 | the preliminary constants (C1)-(C2), defined before X
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The (C1)-(C2) definition is also represented by bpW:w7:constdef#base so that X and the exceptional affine constants can depend on it without depending on (C3)-(C6). No positivity assertion is added to the base definition.
```

```text
NODE: bpW:w7:Xdef
KIND: definition
TITLE: Exceptional set
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:Xdef@L398-L401
PROOF_SOURCE: -
CONTRACT_ID: bpW:w7:Xdef
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W7 standing data (L33-L41): m > 0, lambda_j = sqrt(j^2+m), corrected A, B, max norms on R^2, Leb, ¦k¦ = ¦k_1¦ + ¦k_2¦; the constants K_*, vartheta, j_* of (C2)
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: defines X = {(k,l) in Z^2 x Lambda : 1 <= ¦k¦ < K_*, <l> < K_*/vartheta, and l in Lambda^+ or l = +-(e_i - e_j) with i > j, j < j_*}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:indexdef, bpW:w7:constdef#base
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:indexdef | blueprint-W/parts/w7-measure.tex#bpW:w7:Xdef@L399-L399 | Lambda^+-, <l>
EDGE: bpW:w7:constdef#base | blueprint-W/parts/w7-measure.tex#bpW:w7:Xdef@L399-L400 | the constants K_*, vartheta and j_* from (C2)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w7:Xfinite
KIND: step
TITLE: Finite
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:Xfinite@L408-L410
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:Xfinite@L408-L410
CONTRACT_ID: stepW:w7:Xfinite
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:dichotomy: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta, frequency pairs, phi_kl
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:dichotomy ((k,l) in Z minus X, l in Lambda); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: X is finite
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:indexdef, bpW:w7:Xdef
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:indexdef | blueprint-W/parts/w7-measure.tex#stepW:w7:Xfinite@L409-L409 | <l> on Lambda^+
EDGE: bpW:w7:Xdef | blueprint-W/parts/w7-measure.tex#stepW:w7:Xfinite@L409-L410 | the support and index cutoffs defining X
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w7:dich-small
KIND: step
TITLE: Small $k$
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:dich-small@L414-L416
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:dich-small@L414-L416
CONTRACT_ID: stepW:w7:dich-small
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:dichotomy: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta, frequency pairs, phi_kl; (k,l) in Z minus X, l in Lambda, and the zone of largek is nonempty; the case condition on ¦k¦ is as stated in this step
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:dichotomy ((k,l) in Z minus X, l in Lambda); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: for ¦k¦ < K_*, (k,l) not in X forces l in Lambda^- with j >= j_*, whence the ¦k¦ bound
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:constdef, bpW:w7:Xdef, stepW:w7:dich-large
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:constdef | blueprint-W/parts/w7-measure.tex#stepW:w7:dich-small@L416-L416 | j_*
EDGE: bpW:w7:Xdef | blueprint-W/parts/w7-measure.tex#stepW:w7:dich-small@L415-L415 | not in X forces a difference with j >= j_*
EDGE: stepW:w7:dich-large | blueprint-W/parts/w7-measure.tex#stepW:w7:dich-small@L415-L416 | largek supplies k != 0 and <l> <= ¦k¦/vartheta
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: bpW:w7:dichotomy
KIND: lemma
TITLE: Dichotomy
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:dichotomy@L403-L406
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:dichotomy@L407-L417
CONTRACT_ID: bpW:w7:dichotomy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta, frequency pairs, phi_kl
SOURCE_QUANTIFIERS: (k,l) in Z minus X, l in Lambda
SOURCE_CONCLUSION: X is finite; if a zone of Lemma bpW:w7:largek for (k,l) is nonempty then k != 0, <l> <= ¦k¦/vartheta and ¦k¦ >= 8 c_Lambda ¦l¦_{-1/2}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:Xdef, stepW:w7:Xfinite, stepW:w7:dich-large, stepW:w7:dich-small, bpW:w7:basic#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:Xdef | blueprint-W/parts/w7-measure.tex#bpW:w7:dichotomy@L404-L404 | X
EDGE: stepW:w7:Xfinite | blueprint-W/parts/w7-measure.tex#bpW:w7:dichotomy@L408-L408 | proof step
EDGE: stepW:w7:dich-large | blueprint-W/parts/w7-measure.tex#bpW:w7:dichotomy@L411-L411 | proof step
EDGE: stepW:w7:dich-small | blueprint-W/parts/w7-measure.tex#bpW:w7:dichotomy@L414-L414 | proof step
EDGE: bpW:w7:basic#data | blueprint-W/parts/w7-measure.tex#bpW:w7:dichotomy@L404-L405 | the fixed frequency pair and zone setting
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w7:X-A3
KIND: step
TITLE: Nondegeneracy
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:X-A3@L431-L435
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:X-A3@L431-L435
CONTRACT_ID: stepW:w7:X-A3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:Xzones: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta, frequency pairs, phi_kl; for (k,l) in X, g_kl(zeta) = <k,zeta> + <l,Omega^0(zeta)> = c_kl + <p_kl,zeta>, p_kl = k + (4/7)(sum l_j/lambda_j) lambda_J; sigma_X, c_X as displayed
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:Xzones (for a frequency pair on D, (k,l) in X, 0 < a <= hat alpha); within the step: (k,l) in X; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: g_kl not identically zero; constant case value nonzero; sigma_X, c_X > 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:nondeg, bpW:w7:freqcoords, bpW:w0:basis#lam, stepW:w7:Xfinite, bpW:w7:Xzones#consts
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:nondeg | blueprint-W/parts/w7-measure.tex#stepW:w7:X-A3@L433-L433 | (iii) (A3)
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w7-measure.tex#stepW:w7:X-A3@L434-L434 | omega^0 bijective
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w7-measure.tex#stepW:w7:X-A3@L434-L434 | lambda occurs directly here (frozen lam)
EDGE: stepW:w7:Xfinite | blueprint-W/parts/w7-measure.tex#stepW:w7:X-A3@L435-L435 | X is finite, used to obtain positive minima
EDGE: bpW:w7:Xzones#consts | blueprint-W/parts/w7-measure.tex#stepW:w7:X-A3@L434-L435 | the defined g_kl, sigma_X and c_X
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w7:X-const
KIND: step
TITLE: Constant case
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:X-const@L436-L438
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:X-const@L436-L438
CONTRACT_ID: stepW:w7:X-const
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:Xzones: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta, frequency pairs, phi_kl; for (k,l) in X, g_kl(zeta) = <k,zeta> + <l,Omega^0(zeta)> = c_kl + <p_kl,zeta>, p_kl = k + (4/7)(sum l_j/lambda_j) lambda_J; sigma_X, c_X as displayed; local case premise p_kl = 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:Xzones (for a frequency pair on D, (k,l) in X, 0 < a <= hat alpha); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Y is empty when p_kl = 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:family, bpW:w7:constdef, stepW:w7:X-A3, bpW:w7:Xdef
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:family | blueprint-W/parts/w7-measure.tex#stepW:w7:X-const@L437-L437 | (H1), (H2)
EDGE: bpW:w7:constdef | blueprint-W/parts/w7-measure.tex#stepW:w7:X-const@L438-L438 | (C4)
EDGE: stepW:w7:X-A3 | blueprint-W/parts/w7-measure.tex#stepW:w7:X-const@L437-L437 | c_X
EDGE: bpW:w7:Xdef | blueprint-W/parts/w7-measure.tex#stepW:w7:X-const@L437-L438 | the exceptional-set cutoffs used in the two inequalities
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w7:X-slope
KIND: step
TITLE: Sloped case
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:X-slope@L439-L443
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:X-slope@L439-L443
CONTRACT_ID: stepW:w7:X-slope
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:Xzones: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta, frequency pairs, phi_kl; for (k,l) in X, g_kl(zeta) = <k,zeta> + <l,Omega^0(zeta)> = c_kl + <p_kl,zeta>, p_kl = k + (4/7)(sum l_j/lambda_j) lambda_J; sigma_X, c_X as displayed; local case premise p_kl != 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:Xzones (for a frequency pair on D, (k,l) in X, 0 < a <= hat alpha); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the measure bound when p_kl != 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:family, bpW:w7:constdef, bpW:w7:slab, bpW:w7:freqcoords, stepW:w7:X-A3, bpW:w7:Xdef
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:family | blueprint-W/parts/w7-measure.tex#stepW:w7:X-slope@L441-L441 | (H1)-(H2)
EDGE: bpW:w7:constdef | blueprint-W/parts/w7-measure.tex#stepW:w7:X-slope@L441-L441 | (C4)
EDGE: bpW:w7:slab | blueprint-W/parts/w7-measure.tex#stepW:w7:X-slope@L442-L442 | slicing
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w7-measure.tex#stepW:w7:X-slope@L443-L443 | (iv)
EDGE: stepW:w7:X-A3 | blueprint-W/parts/w7-measure.tex#stepW:w7:X-slope@L440-L442 | sigma_X > 0 discharges the positive-slope premise of slab
EDGE: bpW:w7:Xdef | blueprint-W/parts/w7-measure.tex#stepW:w7:X-slope@L441-L442 | the bounds on ¦k¦ and <l> for (k,l) in X
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w7:sep-concl
KIND: step
TITLE: Conclude
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:sep-concl@L353-L355
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:sep-concl@L353-L355
CONTRACT_ID: stepW:w7:sep-concl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:sep: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta, frequency pairs, phi_kl
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:sep (for a frequency pair on D and l in Lambda); within the step: l; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the separation; S_{0l}, R_{0l} empty
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:unpert-bounds, stepW:w7:sep-drift, bpW:w7:zones, bpW:w7:indexdef, bpW:w7:constdef
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:unpert-bounds | blueprint-W/parts/w7-measure.tex#stepW:w7:sep-concl@L354-L354 | (ii)
EDGE: stepW:w7:sep-drift | blueprint-W/parts/w7-measure.tex#stepW:w7:sep-concl@L354-L354 | the drift
EDGE: bpW:w7:zones | blueprint-W/parts/w7-measure.tex#stepW:w7:sep-concl@L354-L355 | S_0l and R_0l are the strict-inequality zones
EDGE: bpW:w7:indexdef | blueprint-W/parts/w7-measure.tex#stepW:w7:sep-concl@L355-L355 | hat w(l) <= <l> and A_0 = 1
EDGE: bpW:w7:constdef | blueprint-W/parts/w7-measure.tex#stepW:w7:sep-concl@L354-L355 | hat alpha and check alpha <= beta_*
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w7:largek-tan
KIND: step
TITLE: Bound the tangential term
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:largek-tan@L365-L367
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:largek-tan@L365-L367
CONTRACT_ID: stepW:w7:largek-tan
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:largek: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta, frequency pairs, phi_kl; l in Lambda, a <= beta_*; the enclosing implication premise {xi in D : ¦phi_kl(xi)¦ < a <l>/A_k} is nonempty
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:largek (for a frequency pair on D); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦<k,omega'>¦ <= W¦k¦
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:unpert-bounds, bpW:w7:family, bpW:w0:basis#lam, bpW:w7:constdef
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:unpert-bounds | blueprint-W/parts/w7-measure.tex#stepW:w7:largek-tan@L366-L366 | (i)
EDGE: bpW:w7:family | blueprint-W/parts/w7-measure.tex#stepW:w7:largek-tan@L366-L366 | (H1)
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w7-measure.tex#stepW:w7:largek-tan@L366-L366 | lambda occurs directly here (frozen lam)
EDGE: bpW:w7:constdef | blueprint-W/parts/w7-measure.tex#stepW:w7:largek-tan@L366-L366 | W = lambda_2 + 1 and alpha <= alpha_0
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w7:largek-cmp
KIND: step
TITLE: Compare
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:largek-cmp@L368-L370
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:largek-cmp@L368-L370
CONTRACT_ID: stepW:w7:largek-cmp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:largek: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta, frequency pairs, phi_kl; l in Lambda, a <= beta_*; the enclosing implication premise {xi in D : ¦phi_kl(xi)¦ < a <l>/A_k} is nonempty
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:largek (for a frequency pair on D); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: W¦k¦ >= beta_* <l>
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:sep, stepW:w7:largek-tan
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:sep | blueprint-W/parts/w7-measure.tex#stepW:w7:largek-cmp@L370-L370 | separation
EDGE: stepW:w7:largek-tan | blueprint-W/parts/w7-measure.tex#stepW:w7:largek-cmp@L369-L369 | the tangential bound
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w7:dich-large
KIND: step
TITLE: Large $k$
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:dich-large@L411-L413
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:dich-large@L411-L413
CONTRACT_ID: stepW:w7:dich-large
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:dichotomy: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta, frequency pairs, phi_kl; (k,l) in Z minus X, l in Lambda, and the zone of largek is nonempty; the case condition on ¦k¦ is as stated in this step
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:dichotomy ((k,l) in Z minus X, l in Lambda); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: k != 0, <l> <= ¦k¦/vartheta, and the ¦k¦ bound when ¦k¦ >= K_*
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:largek, bpW:w7:constdef
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:largek | blueprint-W/parts/w7-measure.tex#stepW:w7:dich-large@L412-L412 | large k
EDGE: bpW:w7:constdef | blueprint-W/parts/w7-measure.tex#stepW:w7:dich-large@L412-L412 | K_* = 16 c_Lambda
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: bpW:w7:Xzones
KIND: lemma
TITLE: Exceptional zones
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:Xzones@L421-L429
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:Xzones@L430-L444
CONTRACT_ID: bpW:w7:Xzones
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta, frequency pairs, phi_kl; for (k,l) in X, g_kl(zeta) = <k,zeta> + <l,Omega^0(zeta)> = c_kl + <p_kl,zeta>, p_kl = k + (4/7)(sum l_j/lambda_j) lambda_J; sigma_X, c_X as displayed
SOURCE_QUANTIFIERS: for a frequency pair on D, (k,l) in X, 0 < a <= hat alpha
SOURCE_CONCLUSION: g_kl is not identically 0; sigma_X, c_X > 0; the zone Y = {xi in D : ¦phi_kl¦ < a<l>/A_k} is empty if p_kl = 0 and Leb(Y) <= 4 rho_zeta a K_*/(vartheta sigma_X D_A) if p_kl != 0
CONSTANT_SCOPE: sigma_X, c_X depend only on m
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:Xdef, bpW:w7:freqcoords, bpW:w7:Xzones#consts, stepW:w7:X-A3, stepW:w7:X-const, stepW:w7:X-slope, bpW:w0:basis#lam, bpW:w7:basic#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:Xdef | blueprint-W/parts/w7-measure.tex#bpW:w7:Xzones@L422-L422 | X
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w7-measure.tex#bpW:w7:Xzones@L423-L423 | (iii)
EDGE: bpW:w7:Xzones#consts | blueprint-W/parts/w7-measure.tex#bpW:w7:Xzones@L424-L424 | sigma_X, c_X
EDGE: stepW:w7:X-A3 | blueprint-W/parts/w7-measure.tex#bpW:w7:Xzones@L431-L431 | proof step
EDGE: stepW:w7:X-const | blueprint-W/parts/w7-measure.tex#bpW:w7:Xzones@L436-L436 | proof step
EDGE: stepW:w7:X-slope | blueprint-W/parts/w7-measure.tex#bpW:w7:Xzones@L439-L439 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w7-measure.tex#bpW:w7:Xzones@L423-L423 | lambda occurs directly here (frozen lam)
EDGE: bpW:w7:basic#data | blueprint-W/parts/w7-measure.tex#bpW:w7:Xzones@L426-L428 | the frequency pair on D, phi_kl and rho_zeta
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w7:plus
KIND: step
TITLE: Plus type
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:plus@L186-L189
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:plus@L186-L189
CONTRACT_ID: stepW:w7:plus
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:unpert-bounds: W7 standing data (L33-L41): m > 0, lambda_j = sqrt(j^2+m), corrected A, B, max norms on R^2, Leb, ¦k¦ = ¦k_1¦ + ¦k_2¦; ¦xi¦_infty <= 1/2, zeta = omega^0(xi); beta_* = 1/(2 sqrt(9+m)), a_kappa = m/2 + 1
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:unpert-bounds (for such xi; l in Lambda; i > j >= 3); within the step: l in Lambda^+; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦<l,Omega^0>¦ >= (8/9)<l> >= 3 beta_* <l>
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w7:ssize, bpW:w0:basis#lambda-facts, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w7:ssize | blueprint-W/parts/w7-measure.tex#stepW:w7:plus@L187-L187 | ¦s¦ <= 1
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w7-measure.tex#stepW:w7:plus@L187-L187 | lambda_j >= j
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w7-measure.tex#stepW:w7:plus@L187-L187 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: bpW:w7:unpert-bounds
KIND: lemma
TITLE: Unperturbed separation and asymptotics
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:unpert-bounds@L172-L181
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:unpert-bounds@L182-L204
CONTRACT_ID: bpW:w7:unpert-bounds
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W7 standing data (L33-L41): m > 0, lambda_j = sqrt(j^2+m), corrected A, B, max norms on R^2, Leb, ¦k¦ = ¦k_1¦ + ¦k_2¦; ¦xi¦_infty <= 1/2, zeta = omega^0(xi); beta_* = 1/(2 sqrt(9+m)), a_kappa = m/2 + 1
SOURCE_QUANTIFIERS: for such xi; l in Lambda; i > j >= 3
SOURCE_CONCLUSION: (i) ¦s(zeta)¦ <= 1 and ¦omega^0(xi)¦_infty <= lambda_2 + 3/10; (ii) ¦<l,Omega^0(xi)>¦ >= 3 beta_* <l>; (iii) ¦Omega^0_i - Omega^0_j - (i-j)¦ <= a_kappa (i-j) j^{-2}; (iv) zeta -> <l,Omega^0> affine with Lipschitz constant (4/7)(lambda_1 + lambda_2)¦l¦_{-1}
CONSTANT_SCOPE: beta_*, a_kappa depend only on m
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:freqcoords, bpW:w7:indexdef, stepW:w7:ssize, stepW:w7:plus, stepW:w7:minus, stepW:w7:kappa, stepW:w7:liplOmega, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w7-measure.tex#bpW:w7:unpert-bounds@L173-L175 | zeta and s
EDGE: bpW:w7:indexdef | blueprint-W/parts/w7-measure.tex#bpW:w7:unpert-bounds@L176-L176 | Lambda, <l>, ¦l¦_{-1}
EDGE: stepW:w7:ssize | blueprint-W/parts/w7-measure.tex#bpW:w7:unpert-bounds@L183-L183 | proof step
EDGE: stepW:w7:plus | blueprint-W/parts/w7-measure.tex#bpW:w7:unpert-bounds@L186-L186 | proof step
EDGE: stepW:w7:minus | blueprint-W/parts/w7-measure.tex#bpW:w7:unpert-bounds@L190-L190 | proof step
EDGE: stepW:w7:kappa | blueprint-W/parts/w7-measure.tex#bpW:w7:unpert-bounds@L195-L195 | proof step
EDGE: stepW:w7:liplOmega | blueprint-W/parts/w7-measure.tex#bpW:w7:unpert-bounds@L201-L201 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w7-measure.tex#bpW:w7:unpert-bounds@L175-L175 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: bpW:w7:constdef#base
KIND: definition
TITLE: Preliminary W7 constants (C1)-(C2)
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:constdef@L214-L217
PROOF_SOURCE: -
CONTRACT_ID: bpW:w7:constdef#base
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0; W7 standing data; corrected A and B
SOURCE_QUANTIFIERS: m fixed before all application data Pi, alpha and frequency families
SOURCE_CONCLUSION: defines tau = 24, varpi = 1/2, beta = 1/4, w = beta/(4 kappa+4-beta) = 1/47 (kappa = 2); lambda_1,lambda_2; D_A,N_A,L_A of freqcoords; beta_* = 1/(2 sqrt(9+m)), a_kappa = m/2+1; W = lambda_2+1; vartheta = beta_*/W; c_Lambda = (4/7)(lambda_1+lambda_2)+1; K_* = 16 c_Lambda; j_* = (16 c_Lambda)^2
CONSTANT_SCOPE: all depend on m only; independent of Pi,alpha and the frequency families
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:freqcoords, bpW:w7:unpert-bounds, bpW:w0:basis#lam, bpW:w0:mass
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w7-measure.tex#bpW:w7:constdef@L215-L215 | D_A,N_A,L_A
EDGE: bpW:w7:unpert-bounds | blueprint-W/parts/w7-measure.tex#bpW:w7:constdef@L216-L216 | beta_* and a_kappa
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w7-measure.tex#bpW:w7:constdef@L215-L217 | lambda_1 and lambda_2
EDGE: bpW:w0:mass | blueprint-W/parts/w7-measure.tex#bpW:w7:constdef@L214-L214 | m > 0 fixed
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: sol-review-W-w7a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Only definitions (C1)-(C2), not the later minima, smallness thresholds or positivity conclusions. This split permits Xdef to consume its actual constants without a cycle.
```

```text
ITEM: bpW:w7:constdef
KIND: definition
SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:constdef@L211-L231
DISPOSITION: NODE bpW:w7:constdef, bpW:w7:constdef#base
REASON: the full constant definition, with (C1)-(C2) additionally represented separately to supply X's cutoffs before (C3)-(C6)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7a
REVIEWER: -
```

## Suspected blueprint errata and deviations

No new suspected blueprint defect. The proposals split definitions and record missing dependencies; they change no mathematical source assertion.

Review deviations: none. No packet, frozen file, manifest, blueprint, generated file or implementation file was edited.

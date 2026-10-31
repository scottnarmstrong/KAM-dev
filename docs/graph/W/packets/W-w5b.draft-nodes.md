NODE: bpW:w5:new-ham
KIND: lemma
TITLE: New Hamiltonian; conjugacy
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L457-L472
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L473-L493
CONTRACT_ID: bpW:w5:new-ham
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w5:n-exp, stepW:w5:n-br, stepW:w5:n-field, stepW:w5:n-conj, bpW:w5:flow, bpW:w4:lie, bpW:w4:index
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w5:n-exp | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L474-L474 | proof step of this result
EDGE: stepW:w5:n-br | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L481-L481 | proof step of this result
EDGE: stepW:w5:n-field | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L485-L485 | proof step of this result
EDGE: stepW:w5:n-conj | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L488-L488 | proof step of this result
EDGE: bpW:w5:flow | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L458-L458 | cited at this line (statement; \ref{bpW:w5:flow})
EDGE: bpW:w4:lie | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L469-L469 | cited at this line (statement; \ref{bpW:w4:lie})
EDGE: bpW:w4:index | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L470-L470 | cited at this line (statement; \ref{bpW:w4:pairing})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:n-exp
KIND: step
TITLE: Expansion
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-exp@L474-L480
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-exp@L474-L480
CONTRACT_ID: stepW:w5:n-exp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:flow, bpW:w5:flow-calc, bpW:w5:ext-ftc
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:flow | blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-exp@L475-L475 | cited at this line (step; \ref{bpW:w5:flow})
EDGE: bpW:w5:flow-calc | blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-exp@L475-L475 | cited at this line (step; \ref{bpW:w5:flow-calc})
EDGE: bpW:w5:ext-ftc | blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-exp@L475-L475 | cited at this line (step; \ref{bpW:w5:ext-ftc})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:n-br
KIND: step
TITLE: Bracket field
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-br@L481-L484
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-br@L481-L484
CONTRACT_ID: stepW:w5:n-br
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w5:c-skew
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w5:c-skew | blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-br@L483-L483 | cited at this line (step; \ref{stepW:w5:c-skew})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:n-field
KIND: step
TITLE: Field of $P_+$
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-field@L485-L487
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-field@L485-L487
CONTRACT_ID: stepW:w5:n-field
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:flow-calc
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:flow-calc | blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-field@L485-L485 | cited at this line (step; \ref{bpW:w5:flow-calc})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:n-conj
KIND: step
TITLE: Conjugacy
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-conj@L488-L492
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-conj@L488-L492
CONTRACT_ID: stepW:w5:n-conj
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:lie
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:lie | blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-conj@L491-L491 | cited at this line (step; \ref{bpW:w4:lie})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w5:pullback
KIND: lemma
TITLE: Pull-back; P96-K (12)
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:pullback@L502-L506
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:pullback@L507-L522
CONTRACT_ID: bpW:w5:pullback
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w5:p-inv, stepW:w5:p-dy, stepW:w5:p-ass, bpW:w5:flow
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w5:p-inv | blueprint-W/parts/w5-kamstep.tex#bpW:w5:pullback@L508-L508 | proof step of this result
EDGE: stepW:w5:p-dy | blueprint-W/parts/w5-kamstep.tex#bpW:w5:pullback@L514-L514 | proof step of this result
EDGE: stepW:w5:p-ass | blueprint-W/parts/w5-kamstep.tex#bpW:w5:pullback@L517-L517 | proof step of this result
EDGE: bpW:w5:flow | blueprint-W/parts/w5-kamstep.tex#bpW:w5:pullback@L503-L503 | cited at this line (statement; \ref{bpW:w5:flow})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:p-inv
KIND: step
TITLE: Inverse in the small scale
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-inv@L508-L513
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-inv@L508-L513
CONTRACT_ID: stepW:w5:p-inv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:omega, bpW:w5:flow, stepW:w5:f-der
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:omega | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-inv@L508-L508 | cited at this line (step; \ref{bpW:w5:omega})
EDGE: bpW:w5:flow | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-inv@L509-L509 | cited at this line (step; \ref{bpW:w5:flow})
EDGE: stepW:w5:f-der | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-inv@L512-L512 | cited at this line (step; \ref{stepW:w5:f-der})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:p-dy
KIND: step
TITLE: Derivative of $Y$
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-dy@L514-L516
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-dy@L514-L516
CONTRACT_ID: stepW:w5:p-dy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:kam-domain, bpW:w1:cauchy
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:kam-domain | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-dy@L514-L514 | cited at this line (step; \ref{bpW:w1:kam-domain})
EDGE: bpW:w1:cauchy | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-dy@L516-L516 | cited at this line (step; \ref{bpW:w1:cauchy})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:p-ass
KIND: step
TITLE: Assemble
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-ass@L517-L521
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-ass@L517-L521
CONTRACT_ID: stepW:w5:p-ass
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w5:commutator
KIND: lemma
TITLE: Commutators
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:commutator@L526-L529
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:commutator@L530-L538
CONTRACT_ID: bpW:w5:commutator
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w5:k-cauchy, stepW:w5:k-bd, bpW:w5:flow
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w5:k-cauchy | blueprint-W/parts/w5-kamstep.tex#bpW:w5:commutator@L531-L531 | proof step of this result
EDGE: stepW:w5:k-bd | blueprint-W/parts/w5-kamstep.tex#bpW:w5:commutator@L534-L534 | proof step of this result
EDGE: bpW:w5:flow | blueprint-W/parts/w5-kamstep.tex#bpW:w5:commutator@L527-L527 | cited at this line (statement; \ref{bpW:w5:flow})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:k-cauchy
KIND: step
TITLE: Cauchy
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:k-cauchy@L531-L533
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:k-cauchy@L531-L533
CONTRACT_ID: stepW:w5:k-cauchy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:kam-domain, bpW:w1:cauchy
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:kam-domain | blueprint-W/parts/w5-kamstep.tex#stepW:w5:k-cauchy@L532-L532 | cited at this line (step; \ref{bpW:w1:kam-domain})
EDGE: bpW:w1:cauchy | blueprint-W/parts/w5-kamstep.tex#stepW:w5:k-cauchy@L533-L533 | cited at this line (step; \ref{bpW:w1:cauchy})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:k-bd
KIND: step
TITLE: Bound
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:k-bd@L534-L537
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:k-bd@L534-L537
CONTRACT_ID: stepW:w5:k-bd
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:taylor, bpW:w5:solve, bpW:w5:lambda-product
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:taylor | blueprint-W/parts/w5-kamstep.tex#stepW:w5:k-bd@L535-L535 | cited at this line (step; \ref{bpW:w5:taylor})
EDGE: bpW:w5:solve | blueprint-W/parts/w5-kamstep.tex#stepW:w5:k-bd@L535-L535 | cited at this line (step; \ref{bpW:w5:solve})
EDGE: bpW:w5:lambda-product | blueprint-W/parts/w5-kamstep.tex#stepW:w5:k-bd@L535-L535 | cited at this line (step; \ref{bpW:w5:lambda-product})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w5:step
KIND: theorem
TITLE: One KAM step
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L543-L566
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L567-L580
CONTRACT_ID: bpW:w5:step
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w5:st-con, stepW:w5:st-1, stepW:w5:st-2, stepW:w5:st-freq, stepW:w5:st-div, bpW:w5:data, bpW:w5:new-ham, bpW:w5:flow, bpW:w5:w4-general, bpW:w4:wave
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w5:st-con | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L568-L568 | proof step of this result
EDGE: stepW:w5:st-1 | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L571-L571 | proof step of this result
EDGE: stepW:w5:st-2 | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L573-L573 | proof step of this result
EDGE: stepW:w5:st-freq | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L575-L575 | proof step of this result
EDGE: stepW:w5:st-div | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L577-L577 | proof step of this result
EDGE: bpW:w5:data | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L544-L544 | cited at this line (statement; \ref{bpW:w5:data})
EDGE: bpW:w5:new-ham | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L548-L548 | cited at this line (statement; \ref{bpW:w5:new-ham})
EDGE: bpW:w5:flow | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L550-L550 | cited at this line (statement; \ref{bpW:w5:flow})
EDGE: bpW:w5:w4-general | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L557-L557 | cited at this line (statement; \ref{bpW:w5:freq})
EDGE: bpW:w4:wave | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L562-L562 | cited at this line (statement; \ref{bpW:w4:wave})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:st-con
KIND: step
TITLE: Construction
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-con@L568-L570
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-con@L568-L570
CONTRACT_ID: stepW:w5:st-con
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:taylor, bpW:w5:solve, bpW:w5:flow, bpW:w5:flow-calc, bpW:w5:new-ham
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:taylor | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-con@L568-L568 | cited at this line (step; \ref{bpW:w5:taylor})
EDGE: bpW:w5:solve | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-con@L568-L568 | cited at this line (step; \ref{bpW:w5:solve})
EDGE: bpW:w5:flow | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-con@L568-L568 | cited at this line (step; \ref{bpW:w5:flow})
EDGE: bpW:w5:flow-calc | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-con@L569-L569 | cited at this line (step; \ref{bpW:w5:flow-calc})
EDGE: bpW:w5:new-ham | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-con@L569-L569 | cited at this line (step; \ref{bpW:w5:new-ham})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:st-1
KIND: step
TITLE: First term
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-1@L571-L572
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-1@L571-L572
CONTRACT_ID: stepW:w5:st-1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:taylor, bpW:w5:pullback
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:taylor | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-1@L572-L572 | cited at this line (step; \ref{bpW:w5:taylor})
EDGE: bpW:w5:pullback | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-1@L572-L572 | cited at this line (step; \ref{bpW:w5:pullback})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:st-2
KIND: step
TITLE: Second term
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-2@L573-L574
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-2@L573-L574
CONTRACT_ID: stepW:w5:st-2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:commutator, bpW:w5:pullback
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:commutator | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-2@L573-L573 | cited at this line (step; \ref{bpW:w5:commutator})
EDGE: bpW:w5:pullback | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-2@L573-L573 | cited at this line (step; \ref{bpW:w5:pullback})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:st-freq
KIND: step
TITLE: Frequencies
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-freq@L575-L576
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-freq@L575-L576
CONTRACT_ID: stepW:w5:st-freq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:solve
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:solve | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-freq@L575-L575 | cited at this line (step; \ref{bpW:w5:solve})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:st-div
KIND: step
TITLE: Divisors
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-div@L577-L579
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-div@L577-L579
CONTRACT_ID: stepW:w5:st-div
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w5:notation
KIND: claim
TITLE: Notation clash in P96-K
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:notation@L585-L590
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:notation@L585-L590
CONTRACT_ID: bpW:w5:notation
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:convergence
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:convergence | blueprint-W/parts/w5-kamstep.tex#bpW:w5:notation@L589-L589 | cited at this line (statement; \ref{bpW:w6:convergence})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: remark: its justification is inline (confirm, or exclude if not a mathematical claim)

NODE: bpW:w5:action-angle
KIND: lemma
TITLE: Action--angle substitution
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L600-L638
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L639-L667
CONTRACT_ID: bpW:w5:action-angle
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w5:a-hol, stepW:w5:a-dom, stepW:w5:a-der, stepW:w5:a-nf, stepW:w5:a-field, stepW:w5:a-conj, bpW:w0:periodone#linearTorus, bpW:w3:coords, bpW:w7:omega0, bpW:w4:from-w3, bpW:w5:initial
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w5:a-hol | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L640-L640 | proof step of this result
EDGE: stepW:w5:a-dom | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L644-L644 | proof step of this result
EDGE: stepW:w5:a-der | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L647-L647 | proof step of this result
EDGE: stepW:w5:a-nf | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L651-L651 | proof step of this result
EDGE: stepW:w5:a-field | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L655-L655 | proof step of this result
EDGE: stepW:w5:a-conj | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L661-L661 | proof step of this result
EDGE: bpW:w0:periodone#linearTorus | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L608-L608 | cited at this line (statement; \ref{bpW:w0:periodone})
EDGE: bpW:w3:coords | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L609-L609 | cited at this line (statement; \ref{bpW:w3:coords})
EDGE: bpW:w7:omega0 | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L623-L623 | cited at this line (statement; \ref{bpW:w7:omega0})
EDGE: bpW:w4:from-w3 | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L632-L632 | cited at this line (statement; \ref{bpW:w4:from-w3})
EDGE: bpW:w5:initial | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L635-L635 | cited at this line (statement; \ref{bpW:w5:initial})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:a-hol
KIND: step
TITLE: Holomorphy and reality
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-hol@L640-L643
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-hol@L640-L643
CONTRACT_ID: stepW:w5:a-hol
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:a-dom
KIND: step
TITLE: Domain
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-dom@L644-L646
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-dom@L644-L646
CONTRACT_ID: stepW:w5:a-dom
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:a-der
KIND: step
TITLE: Derivative
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-der@L647-L650
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-der@L647-L650
CONTRACT_ID: stepW:w5:a-der
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:index
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:index | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-der@L650-L650 | cited at this line (step; \ref{bpW:w4:pairing})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:a-nf
KIND: step
TITLE: Normal form
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-nf@L651-L654
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-nf@L651-L654
CONTRACT_ID: stepW:w5:a-nf
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:main, bpW:w0n:AB
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:main | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-nf@L653-L653 | cited at this line (step; \ref{bpW:w3:main})
EDGE: bpW:w0n:AB | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-nf@L653-L653 | cited at this line (step; \ref{bpW:w0n:AB})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:a-field
KIND: step
TITLE: Fields
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-field@L655-L660
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-field@L655-L660
CONTRACT_ID: stepW:w5:a-field
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:main
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:main | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-field@L655-L655 | cited at this line (step; \ref{bpW:w3:main})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:a-conj
KIND: step
TITLE: Conjugacy
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-conj@L661-L666
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-conj@L661-L666
CONTRACT_ID: stepW:w5:a-conj
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:Lambda, bpW:w5:new-ham, bpW:w3:omega
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:Lambda | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-conj@L663-L663 | cited at this line (step; \ref{bpW:w3:Lambda})
EDGE: bpW:w5:new-ham | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-conj@L663-L663 | cited at this line (step; \ref{bpW:w5:new-ham})
EDGE: bpW:w3:omega | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-conj@L666-L666 | cited at this line (step; \ref{bpW:w3:omega})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w5:initial
KIND: proposition
TITLE: The initial perturbation; KP96 \S7, Step~3
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L673-L682
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L683-L703
CONTRACT_ID: bpW:w5:initial
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w5:i-q, stepW:w5:i-g, stepW:w5:i-k, stepW:w5:i-par, stepW:w5:i-freq, bpW:w4:melnikov, bpW:w5:w4-general, bpW:w4:wave
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w5:i-q | blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L684-L684 | proof step of this result
EDGE: stepW:w5:i-g | blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L689-L689 | proof step of this result
EDGE: stepW:w5:i-k | blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L692-L692 | proof step of this result
EDGE: stepW:w5:i-par | blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L697-L697 | proof step of this result
EDGE: stepW:w5:i-freq | blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L702-L702 | proof step of this result
EDGE: bpW:w4:melnikov | blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L680-L680 | cited at this line (statement; \ref{bpW:w4:freq})
EDGE: bpW:w5:w4-general | blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L680-L680 | cited at this line (statement; \ref{bpW:w5:freq})
EDGE: bpW:w4:wave | blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L681-L681 | cited at this line (statement; \ref{bpW:w4:wave})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:i-q
KIND: step
TITLE: The polynomial part
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-q@L684-L688
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-q@L684-L688
CONTRACT_ID: stepW:w5:i-q
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:freqcoords, bpW:w4:index
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-q@L685-L685 | cited at this line (step; \ref{bpW:w7:freqcoords})
EDGE: bpW:w4:index | blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-q@L686-L686 | cited at this line (step; \ref{bpW:w4:zu})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:i-g
KIND: step
TITLE: $G^{\rm nor}$
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-g@L689-L691
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-g@L689-L691
CONTRACT_ID: stepW:w5:i-g
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:main, bpW:w5:action-angle
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:main | blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-g@L690-L690 | cited at this line (step; \ref{bpW:w3:main})
EDGE: bpW:w5:action-angle | blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-g@L691-L691 | cited at this line (step; \ref{bpW:w5:action-angle})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:i-k
KIND: step
TITLE: $K$
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-k@L692-L696
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-k@L692-L696
CONTRACT_ID: stepW:w5:i-k
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:action-angle
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:action-angle | blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-k@L692-L692 | cited at this line (step; \ref{bpW:w5:action-angle})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:i-par
KIND: step
TITLE: Parameters
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-par@L697-L701
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-par@L697-L701
CONTRACT_ID: stepW:w5:i-par
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:cauchy
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:cauchy | blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-par@L700-L700 | cited at this line (step; \ref{bpW:w1:cauchy})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:i-freq
KIND: step
TITLE: Frequencies
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-freq@L702-L702
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-freq@L702-L702
CONTRACT_ID: stepW:w5:i-freq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:wave, bpW:w7:freqcoords
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:wave | blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-freq@L702-L702 | cited at this line (step; \ref{bpW:w4:wave})
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-freq@L702-L702 | cited at this line (step; \ref{bpW:w7:freqcoords})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

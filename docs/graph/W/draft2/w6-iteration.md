NODE: bpW:w6:sequences
KIND: definition
TITLE: Iteration sequences
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:sequences@L31-L41
PROOF_SOURCE: -
CONTRACT_ID: bpW:w6:sequences
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

NODE: bpW:w6:iter-lemma
KIND: lemma
TITLE: Iterative lemma
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:iter-lemma@L47-L67
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:iter-lemma@L68-L84
CONTRACT_ID: bpW:w6:iter-lemma
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w6:il-small, stepW:w6:il-err, stepW:w6:il-lip, stepW:w6:il-div, stepW:w6:il-tr, bpW:w6:sequences, bpW:w5:w4-general, bpW:w5:step, bpW:w6:k0
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w6:il-small | blueprint-W/parts/w6-iteration.tex#bpW:w6:iter-lemma@L69-L69 | proof step of this result
EDGE: stepW:w6:il-err | blueprint-W/parts/w6-iteration.tex#bpW:w6:iter-lemma@L72-L72 | proof step of this result
EDGE: stepW:w6:il-lip | blueprint-W/parts/w6-iteration.tex#bpW:w6:iter-lemma@L76-L76 | proof step of this result
EDGE: stepW:w6:il-div | blueprint-W/parts/w6-iteration.tex#bpW:w6:iter-lemma@L79-L79 | proof step of this result
EDGE: stepW:w6:il-tr | blueprint-W/parts/w6-iteration.tex#bpW:w6:iter-lemma@L83-L83 | proof step of this result
EDGE: bpW:w6:sequences | blueprint-W/parts/w6-iteration.tex#bpW:w6:iter-lemma@L48-L48 | cited at this line (statement; \ref{bpW:w6:sequences})
EDGE: bpW:w5:w4-general | blueprint-W/parts/w6-iteration.tex#bpW:w6:iter-lemma@L50-L50 | cited at this line (statement; \ref{bpW:w5:freq})
EDGE: bpW:w5:step | blueprint-W/parts/w6-iteration.tex#bpW:w6:iter-lemma@L56-L56 | cited at this line (statement; \ref{bpW:w5:step})
EDGE: bpW:w6:k0 | blueprint-W/parts/w6-iteration.tex#bpW:w6:iter-lemma@L62-L62 | cited at this line (statement; \ref{bpW:w6:k0})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:il-small
KIND: step
TITLE: Smallness
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:il-small@L69-L71
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:il-small@L69-L71
CONTRACT_ID: stepW:w6:il-small
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:data, bpW:w5:step
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:data | blueprint-W/parts/w6-iteration.tex#stepW:w6:il-small@L70-L70 | cited at this line (step; \ref{bpW:w5:small})
EDGE: bpW:w5:step | blueprint-W/parts/w6-iteration.tex#stepW:w6:il-small@L71-L71 | cited at this line (step; \ref{bpW:w5:step})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:il-err
KIND: step
TITLE: New error
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:il-err@L72-L75
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:il-err@L72-L75
CONTRACT_ID: stepW:w6:il-err
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:step
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:step | blueprint-W/parts/w6-iteration.tex#stepW:w6:il-err@L72-L72 | cited at this line (step; \ref{bpW:w5:newerror})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:il-lip
KIND: step
TITLE: Lipschitz constants
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:il-lip@L76-L78
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:il-lip@L76-L78
CONTRACT_ID: stepW:w6:il-lip
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:step
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:step | blueprint-W/parts/w6-iteration.tex#stepW:w6:il-lip@L76-L76 | cited at this line (step; \ref{bpW:w5:step})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:il-div
KIND: step
TITLE: Divisors
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:il-div@L79-L82
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:il-div@L79-L82
CONTRACT_ID: stepW:w6:il-div
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:step
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:step | blueprint-W/parts/w6-iteration.tex#stepW:w6:il-div@L81-L81 | cited at this line (step; \ref{bpW:w5:step})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:il-tr
KIND: step
TITLE: Transformations
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:il-tr@L83-L83
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:il-tr@L83-L83
CONTRACT_ID: stepW:w6:il-tr
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:step
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:step | blueprint-W/parts/w6-iteration.tex#stepW:w6:il-tr@L83-L83 | cited at this line (step; \ref{bpW:w5:step})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w6:k0
KIND: lemma
TITLE: The conditions with $k=0$
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:k0@L89-L93
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:k0@L94-L98
CONTRACT_ID: bpW:w6:k0
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:iter-lemma
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:iter-lemma | blueprint-W/parts/w6-iteration.tex#bpW:w6:k0@L90-L90 | cited at this line (statement; \ref{bpW:w6:iter-lemma})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w6:convergence
KIND: proposition
TITLE: Iteration and convergence; P96-K Theorem~A, proof
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:convergence@L103-L133
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:convergence@L134-L161
CONTRACT_ID: bpW:w6:convergence
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w6:c-ind, stepW:w6:c-par, stepW:w6:c-freq, stepW:w6:c-dom, stepW:w6:c-op, stepW:w6:c-cauchy, stepW:w6:c-lim, stepW:w6:c-cont, bpW:w6:sequences, bpW:w5:w4-general, bpW:w6:k0, bpW:w6:iter-lemma
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w6:c-ind | blueprint-W/parts/w6-iteration.tex#bpW:w6:convergence@L135-L135 | proof step of this result
EDGE: stepW:w6:c-par | blueprint-W/parts/w6-iteration.tex#bpW:w6:convergence@L137-L137 | proof step of this result
EDGE: stepW:w6:c-freq | blueprint-W/parts/w6-iteration.tex#bpW:w6:convergence@L139-L139 | proof step of this result
EDGE: stepW:w6:c-dom | blueprint-W/parts/w6-iteration.tex#bpW:w6:convergence@L143-L143 | proof step of this result
EDGE: stepW:w6:c-op | blueprint-W/parts/w6-iteration.tex#bpW:w6:convergence@L147-L147 | proof step of this result
EDGE: stepW:w6:c-cauchy | blueprint-W/parts/w6-iteration.tex#bpW:w6:convergence@L151-L151 | proof step of this result
EDGE: stepW:w6:c-lim | blueprint-W/parts/w6-iteration.tex#bpW:w6:convergence@L154-L154 | proof step of this result
EDGE: stepW:w6:c-cont | blueprint-W/parts/w6-iteration.tex#bpW:w6:convergence@L158-L158 | proof step of this result
EDGE: bpW:w6:sequences | blueprint-W/parts/w6-iteration.tex#bpW:w6:convergence@L104-L104 | cited at this line (statement; \ref{bpW:w6:sequences})
EDGE: bpW:w5:w4-general | blueprint-W/parts/w6-iteration.tex#bpW:w6:convergence@L105-L105 | cited at this line (statement; \ref{bpW:w5:freq})
EDGE: bpW:w6:k0 | blueprint-W/parts/w6-iteration.tex#bpW:w6:convergence@L106-L106 | cited at this line (statement; \ref{bpW:w6:k0})
EDGE: bpW:w6:iter-lemma | blueprint-W/parts/w6-iteration.tex#bpW:w6:convergence@L109-L109 | cited at this line (statement; \ref{bpW:w6:iter-lemma})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:c-ind
KIND: step
TITLE: Induction
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-ind@L135-L136
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-ind@L135-L136
CONTRACT_ID: stepW:w6:c-ind
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:iter-lemma, bpW:w6:k0
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:iter-lemma | blueprint-W/parts/w6-iteration.tex#stepW:w6:c-ind@L135-L135 | cited at this line (step; \ref{bpW:w6:melnikov})
EDGE: bpW:w6:k0 | blueprint-W/parts/w6-iteration.tex#stepW:w6:c-ind@L136-L136 | cited at this line (step; \ref{bpW:w6:k0})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:c-par
KIND: step
TITLE: Parameters
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-par@L137-L138
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-par@L137-L138
CONTRACT_ID: stepW:w6:c-par
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:ext-borel
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:ext-borel | blueprint-W/parts/w6-iteration.tex#stepW:w6:c-par@L138-L138 | cited at this line (step; \ref{bpW:w7:ext-borel})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:c-freq
KIND: step
TITLE: Frequencies
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-freq@L139-L142
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-freq@L139-L142
CONTRACT_ID: stepW:w6:c-freq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:iter-lemma
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:iter-lemma | blueprint-W/parts/w6-iteration.tex#stepW:w6:c-freq@L139-L139 | cited at this line (step; \ref{bpW:w6:iter-lemma})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:c-dom
KIND: step
TITLE: Domains
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-dom@L143-L146
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-dom@L143-L146
CONTRACT_ID: stepW:w6:c-dom
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:step
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:step | blueprint-W/parts/w6-iteration.tex#stepW:w6:c-dom@L143-L143 | cited at this line (step; \ref{bpW:w5:step})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:c-op
KIND: step
TITLE: Operator bounds
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-op@L147-L150
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-op@L147-L150
CONTRACT_ID: stepW:w6:c-op
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:iter-lemma, bpW:w5:omega, bpW:w5:step
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:iter-lemma | blueprint-W/parts/w6-iteration.tex#stepW:w6:c-op@L148-L148 | cited at this line (step; \ref{bpW:w6:iter-lemma})
EDGE: bpW:w5:omega | blueprint-W/parts/w6-iteration.tex#stepW:w6:c-op@L148-L148 | cited at this line (step; \ref{bpW:w5:omega})
EDGE: bpW:w5:step | blueprint-W/parts/w6-iteration.tex#stepW:w6:c-op@L150-L150 | cited at this line (step; \ref{bpW:w5:step})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:c-cauchy
KIND: step
TITLE: Cauchy sequence
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-cauchy@L151-L153
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-cauchy@L151-L153
CONTRACT_ID: stepW:w6:c-cauchy
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

NODE: stepW:w6:c-lim
KIND: step
TITLE: Limit
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-lim@L154-L157
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-lim@L154-L157
CONTRACT_ID: stepW:w6:c-lim
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:uniform-limit
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:uniform-limit | blueprint-W/parts/w6-iteration.tex#stepW:w6:c-lim@L155-L155 | cited at this line (step; \ref{bpW:w1:uniform-limit})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:c-cont
KIND: step
TITLE: Continuity in $\xi$
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-cont@L158-L160
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-cont@L158-L160
CONTRACT_ID: stepW:w6:c-cont
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:flow
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:flow | blueprint-W/parts/w6-iteration.tex#stepW:w6:c-cont@L158-L158 | cited at this line (step; \ref{bpW:w5:flow})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w6:strong
KIND: lemma
TITLE: Strong conjugacy at regular points
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:strong@L170-L175
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:strong@L176-L179
CONTRACT_ID: bpW:w6:strong
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w5:omnd
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w5:omnd | blueprint-W/parts/w6-iteration.tex#bpW:w6:strong@L178-L178 | cited at this line (proof; \ref{stepW:w5:omnd})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w6:invariance
KIND: proposition
TITLE: Invariant tori in KAM coordinates
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:invariance@L182-L187
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:invariance@L188-L204
CONTRACT_ID: bpW:w6:invariance
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w6:i-weak, stepW:w6:i-torus, stepW:w6:i-lim, bpW:w6:convergence
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w6:i-weak | blueprint-W/parts/w6-iteration.tex#bpW:w6:invariance@L189-L189 | proof step of this result
EDGE: stepW:w6:i-torus | blueprint-W/parts/w6-iteration.tex#bpW:w6:invariance@L197-L197 | proof step of this result
EDGE: stepW:w6:i-lim | blueprint-W/parts/w6-iteration.tex#bpW:w6:invariance@L200-L200 | proof step of this result
EDGE: bpW:w6:convergence | blueprint-W/parts/w6-iteration.tex#bpW:w6:invariance@L183-L183 | cited at this line (statement; \ref{bpW:w6:convergence})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:i-weak
KIND: step
TITLE: Weak chain
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:i-weak@L189-L196
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:i-weak@L189-L196
CONTRACT_ID: stepW:w6:i-weak
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:step, bpW:w6:convergence, stepW:w5:n-conj
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:step | blueprint-W/parts/w6-iteration.tex#stepW:w6:i-weak@L190-L190 | cited at this line (step; \ref{bpW:w5:step})
EDGE: bpW:w6:convergence | blueprint-W/parts/w6-iteration.tex#stepW:w6:i-weak@L193-L193 | cited at this line (step; \ref{bpW:w6:convergence})
EDGE: stepW:w5:n-conj | blueprint-W/parts/w6-iteration.tex#stepW:w6:i-weak@L193-L193 | cited at this line (step; \ref{stepW:w5:n-conj})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:i-torus
KIND: step
TITLE: Torus points
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:i-torus@L197-L199
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:i-torus@L197-L199
CONTRACT_ID: stepW:w6:i-torus
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:strong, bpW:w6:convergence
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:strong | blueprint-W/parts/w6-iteration.tex#stepW:w6:i-torus@L198-L198 | cited at this line (step; \ref{bpW:w6:strong})
EDGE: bpW:w6:convergence | blueprint-W/parts/w6-iteration.tex#stepW:w6:i-torus@L198-L198 | cited at this line (step; \ref{bpW:w6:convergence})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:i-lim
KIND: step
TITLE: Limit
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:i-lim@L200-L203
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:i-lim@L200-L203
CONTRACT_ID: stepW:w6:i-lim
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
EDGE: bpW:w4:lie | blueprint-W/parts/w6-iteration.tex#stepW:w6:i-lim@L202-L202 | cited at this line (step; \ref{bpW:w4:lie})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w6:constants
KIND: definition
TITLE: W6 constants
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:constants@L211-L218
PROOF_SOURCE: -
CONTRACT_ID: bpW:w6:constants
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:constdef, bpW:w4:wave, bpW:w6:sequences
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:constdef | blueprint-W/parts/w6-iteration.tex#bpW:w6:constants@L212-L212 | cited at this line (statement; \ref{bpW:w7:constdef})
EDGE: bpW:w4:wave | blueprint-W/parts/w6-iteration.tex#bpW:w6:constants@L213-L213 | cited at this line (statement; \ref{bpW:w4:wave})
EDGE: bpW:w6:sequences | blueprint-W/parts/w6-iteration.tex#bpW:w6:constants@L214-L214 | cited at this line (statement; \ref{bpW:w6:sequences})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w6:prep-step
KIND: lemma
TITLE: Preparatory step; P96-K \S6
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L220-L245
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L246-L267
CONTRACT_ID: bpW:w6:prep-step
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w6:p-data, stepW:w6:p-div, stepW:w6:p-step, stepW:w6:p-lipp, stepW:w6:p-size, stepW:w6:p-gap, bpW:w7:zones, bpW:w5:initial, bpW:w5:step, bpW:w5:new-ham, bpW:w7:melnikov, bpW:w5:w4-modified, bpW:w4:wave, bpW:w5:w4-general
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w6:p-data | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L247-L247 | proof step of this result
EDGE: stepW:w6:p-div | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L250-L250 | proof step of this result
EDGE: stepW:w6:p-step | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L253-L253 | proof step of this result
EDGE: stepW:w6:p-lipp | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L258-L258 | proof step of this result
EDGE: stepW:w6:p-size | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L260-L260 | proof step of this result
EDGE: stepW:w6:p-gap | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L264-L264 | proof step of this result
EDGE: bpW:w7:zones | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L222-L222 | cited at this line (statement; \ref{bpW:w7:zones})
EDGE: bpW:w5:initial | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L226-L226 | cited at this line (statement; \ref{bpW:w5:initial})
EDGE: bpW:w5:step | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L227-L227 | cited at this line (statement; \ref{bpW:w5:step})
EDGE: bpW:w5:new-ham | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L230-L230 | cited at this line (statement; \ref{bpW:w5:new-ham})
EDGE: bpW:w7:melnikov | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L233-L233 | cited at this line (statement; \ref{bpW:w7:melnikov})
EDGE: bpW:w5:w4-modified | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L234-L234 | cited at this line (statement; \ref{bpW:w5:modified})
EDGE: bpW:w4:wave | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L235-L235 | cited at this line (statement; \ref{bpW:w4:wave})
EDGE: bpW:w5:w4-general | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L238-L238 | cited at this line (statement; \ref{bpW:w5:freq})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:p-data
KIND: step
TITLE: Data
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-data@L247-L249
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-data@L247-L249
CONTRACT_ID: stepW:w6:p-data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:data, bpW:w4:melnikov, bpW:w4:wave
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:data | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-data@L248-L248 | cited at this line (step; \ref{bpW:w5:small})
EDGE: bpW:w4:melnikov | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-data@L249-L249 | cited at this line (step; \ref{bpW:w4:freq})
EDGE: bpW:w4:wave | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-data@L249-L249 | cited at this line (step; \ref{bpW:w4:wave})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:p-div
KIND: step
TITLE: Divisors
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-div@L250-L252
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-div@L250-L252
CONTRACT_ID: stepW:w6:p-div
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:w4-modified
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:w4-modified | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-div@L251-L251 | cited at this line (step; \ref{bpW:w5:modified})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:p-step
KIND: step
TITLE: Step
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-step@L253-L257
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-step@L253-L257
CONTRACT_ID: stepW:w6:p-step
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:step, bpW:w5:w4-modified, bpW:w5:taylor, bpW:w4:lemma1
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:step | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-step@L253-L253 | cited at this line (step; \ref{bpW:w5:step})
EDGE: bpW:w5:w4-modified | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-step@L254-L254 | cited at this line (step; \ref{bpW:w5:w4-modified})
EDGE: bpW:w5:taylor | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-step@L256-L256 | cited at this line (step; \ref{bpW:w5:taylor})
EDGE: bpW:w4:lemma1 | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-step@L256-L256 | cited at this line (step; \ref{bpW:w4:lemma1})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:p-lipp
KIND: step
TITLE: Transformation
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-lipp@L258-L259
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-lipp@L258-L259
CONTRACT_ID: stepW:w6:p-lipp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:step
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:step | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-lipp@L258-L258 | cited at this line (step; \ref{bpW:w5:step})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:p-size
KIND: step
TITLE: Size
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-size@L260-L263
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-size@L260-L263
CONTRACT_ID: stepW:w6:p-size
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:step
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:step | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-size@L260-L260 | cited at this line (step; \ref{bpW:w5:newerror})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:p-gap
KIND: step
TITLE: Lipschitz part
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-gap@L264-L266
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-gap@L264-L266
CONTRACT_ID: stepW:w6:p-gap
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:w4-modified, bpW:w5:step, stepW:w6:p-size
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:w4-modified | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-gap@L264-L264 | cited at this line (step; \ref{bpW:w5:w4-modified})
EDGE: bpW:w5:step | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-gap@L264-L264 | cited at this line (step; \ref{bpW:w5:newerror})
EDGE: stepW:w6:p-size | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-gap@L265-L265 | cited at this line (step; \ref{stepW:w6:p-size})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w6:wave-iteration
KIND: definition
TITLE: The wave iteration
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:wave-iteration@L275-L282
PROOF_SOURCE: -
CONTRACT_ID: bpW:w6:wave-iteration
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:prep-step, bpW:w6:convergence, bpW:w6:constants
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:prep-step | blueprint-W/parts/w6-iteration.tex#bpW:w6:wave-iteration@L276-L276 | cited at this line (statement; \ref{bpW:w6:prep-step})
EDGE: bpW:w6:convergence | blueprint-W/parts/w6-iteration.tex#bpW:w6:wave-iteration@L276-L276 | cited at this line (statement; \ref{bpW:w6:convergence})
EDGE: bpW:w6:constants | blueprint-W/parts/w6-iteration.tex#bpW:w6:wave-iteration@L277-L277 | cited at this line (statement; \ref{bpW:w6:constants})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w6:applicable
KIND: lemma
TITLE: Applicability
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:applicable@L284-L286
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:applicable@L287-L293
CONTRACT_ID: bpW:w6:applicable
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:convergence, bpW:w6:wave-iteration, bpW:w7:unpert-bounds
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:convergence | blueprint-W/parts/w6-iteration.tex#bpW:w6:applicable@L285-L285 | cited at this line (statement; \ref{bpW:w6:convergence})
EDGE: bpW:w6:wave-iteration | blueprint-W/parts/w6-iteration.tex#bpW:w6:applicable@L285-L285 | cited at this line (statement; \ref{bpW:w6:wave-iteration})
EDGE: bpW:w7:unpert-bounds | blueprint-W/parts/w6-iteration.tex#bpW:w6:applicable@L289-L289 | cited at this line (proof; \ref{bpW:w7:unpert-bounds})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w6:freq-lip
KIND: lemma
TITLE: Lipschitz frequencies; W7's (H1)--(H2)
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:freq-lip@L296-L304
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:freq-lip@L305-L314
CONTRACT_ID: bpW:w6:freq-lip
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w6:fl-size, stepW:w6:fl-lip, stepW:w6:fl-borel, bpW:w6:wave-iteration, bpW:w6:sequences, bpW:w7:family
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w6:fl-size | blueprint-W/parts/w6-iteration.tex#bpW:w6:freq-lip@L306-L306 | proof step of this result
EDGE: stepW:w6:fl-lip | blueprint-W/parts/w6-iteration.tex#bpW:w6:freq-lip@L309-L309 | proof step of this result
EDGE: stepW:w6:fl-borel | blueprint-W/parts/w6-iteration.tex#bpW:w6:freq-lip@L313-L313 | proof step of this result
EDGE: bpW:w6:wave-iteration | blueprint-W/parts/w6-iteration.tex#bpW:w6:freq-lip@L297-L297 | cited at this line (statement; \ref{bpW:w6:wave-iteration})
EDGE: bpW:w6:sequences | blueprint-W/parts/w6-iteration.tex#bpW:w6:freq-lip@L298-L298 | cited at this line (statement; \ref{bpW:w6:sequences})
EDGE: bpW:w7:family | blueprint-W/parts/w6-iteration.tex#bpW:w6:freq-lip@L300-L300 | cited at this line (statement; \ref{bpW:w7:family})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:fl-size
KIND: step
TITLE: Sizes
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-size@L306-L308
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-size@L306-L308
CONTRACT_ID: stepW:w6:fl-size
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:prep-step, bpW:w6:convergence
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:prep-step | blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-size@L306-L306 | cited at this line (step; \ref{bpW:w6:prep-step})
EDGE: bpW:w6:convergence | blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-size@L307-L307 | cited at this line (step; \ref{bpW:w6:convergence})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:fl-lip
KIND: step
TITLE: Lipschitz
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-lip@L309-L312
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-lip@L309-L312
CONTRACT_ID: stepW:w6:fl-lip
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:constants
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:constants | blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-lip@L312-L312 | cited at this line (step; \ref{bpW:w6:constants})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:fl-borel
KIND: step
TITLE: Borel
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-borel@L313-L313
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-borel@L313-L313
CONTRACT_ID: stepW:w6:fl-borel
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:convergence, bpW:w7:measurable
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:convergence | blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-borel@L313-L313 | cited at this line (step; \ref{bpW:w6:convergence})
EDGE: bpW:w7:measurable | blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-borel@L313-L313 | cited at this line (step; \ref{bpW:w7:measurable})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w6:exclusion
KIND: lemma
TITLE: Exclusion
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:exclusion@L318-L321
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:exclusion@L322-L326
CONTRACT_ID: bpW:w6:exclusion
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:wave-iteration, bpW:w6:freq-lip, bpW:w6:convergence
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:wave-iteration | blueprint-W/parts/w6-iteration.tex#bpW:w6:exclusion@L319-L319 | cited at this line (statement; \ref{bpW:w6:wave-iteration})
EDGE: bpW:w6:freq-lip | blueprint-W/parts/w6-iteration.tex#bpW:w6:exclusion@L320-L320 | cited at this line (statement; \ref{bpW:w6:freq-lip})
EDGE: bpW:w6:convergence | blueprint-W/parts/w6-iteration.tex#bpW:w6:exclusion@L323-L323 | cited at this line (proof; \ref{bpW:w6:convergence})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w6:final-freq
KIND: lemma
TITLE: Final frequencies
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:final-freq@L330-L333
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:final-freq@L334-L337
CONTRACT_ID: bpW:w6:final-freq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:convergence, bpW:w6:freq-lip, bpW:w7:freqcoords
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:convergence | blueprint-W/parts/w6-iteration.tex#bpW:w6:final-freq@L335-L335 | cited at this line (proof; \ref{bpW:w6:convergence})
EDGE: bpW:w6:freq-lip | blueprint-W/parts/w6-iteration.tex#bpW:w6:final-freq@L336-L336 | cited at this line (proof; \ref{bpW:w6:freq-lip})
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w6-iteration.tex#bpW:w6:final-freq@L336-L336 | cited at this line (proof; \ref{bpW:w7:freqcoords})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w6:tori
KIND: theorem
TITLE: Invariant tori in Birkhoff coordinates
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L342-L361
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L362-L377
CONTRACT_ID: bpW:w6:tori
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w6:t-hol, stepW:w6:t-cont, stepW:w6:t-prep, stepW:w6:t-bk, stepW:w6:t-close, stepW:w6:t-an, bpW:w6:wave-iteration, bpW:w5:action-angle, bpW:w5:initial, bpW:w6:convergence
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w6:t-hol | blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L363-L363 | proof step of this result
EDGE: stepW:w6:t-cont | blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L366-L366 | proof step of this result
EDGE: stepW:w6:t-prep | blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L368-L368 | proof step of this result
EDGE: stepW:w6:t-bk | blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L371-L371 | proof step of this result
EDGE: stepW:w6:t-close | blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L372-L372 | proof step of this result
EDGE: stepW:w6:t-an | blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L374-L374 | proof step of this result
EDGE: bpW:w6:wave-iteration | blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L343-L343 | cited at this line (statement; \ref{bpW:w6:wave-iteration})
EDGE: bpW:w5:action-angle | blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L343-L343 | cited at this line (statement; \ref{bpW:w5:action-angle})
EDGE: bpW:w5:initial | blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L344-L344 | cited at this line (statement; \ref{bpW:w5:initial})
EDGE: bpW:w6:convergence | blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L353-L353 | cited at this line (statement; \ref{bpW:w6:convergence})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:t-hol
KIND: step
TITLE: Holomorphy
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-hol@L363-L365
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-hol@L363-L365
CONTRACT_ID: stepW:w6:t-hol
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
EDGE: bpW:w6:convergence | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-hol@L363-L363 | cited at this line (step; \ref{bpW:w6:convergence})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:t-cont
KIND: step
TITLE: Continuity
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-cont@L366-L367
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-cont@L366-L367
CONTRACT_ID: stepW:w6:t-cont
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:convergence, bpW:w6:prep-step, bpW:w6:final-freq
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:convergence | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-cont@L366-L366 | cited at this line (step; \ref{bpW:w6:convergence})
EDGE: bpW:w6:prep-step | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-cont@L366-L366 | cited at this line (step; \ref{bpW:w6:prep-step})
EDGE: bpW:w6:final-freq | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-cont@L367-L367 | cited at this line (step; \ref{bpW:w6:final-freq})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:t-prep
KIND: step
TITLE: Invariance, prep step
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-prep@L368-L370
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-prep@L368-L370
CONTRACT_ID: stepW:w6:t-prep
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:invariance, bpW:w5:new-ham, bpW:w6:strong
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:invariance | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-prep@L368-L368 | cited at this line (step; \ref{bpW:w6:invariance})
EDGE: bpW:w5:new-ham | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-prep@L369-L369 | cited at this line (step; \ref{bpW:w5:new-ham})
EDGE: bpW:w6:strong | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-prep@L369-L369 | cited at this line (step; \ref{bpW:w6:strong})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:t-bk
KIND: step
TITLE: Invariance, Birkhoff
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-bk@L371-L371
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-bk@L371-L371
CONTRACT_ID: stepW:w6:t-bk
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
EDGE: bpW:w5:action-angle | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-bk@L371-L371 | cited at this line (step; \ref{bpW:w5:action-angle})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:t-close
KIND: step
TITLE: Closeness
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-close@L372-L373
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-close@L372-L373
CONTRACT_ID: stepW:w6:t-close
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:prep-step, bpW:w6:convergence
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:prep-step | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-close@L372-L372 | cited at this line (step; \ref{bpW:w6:prep-step})
EDGE: bpW:w6:convergence | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-close@L372-L372 | cited at this line (step; \ref{bpW:w6:convergence})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:t-an
KIND: step
TITLE: Analyticity
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-an@L374-L376
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-an@L374-L376
CONTRACT_ID: stepW:w6:t-an
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:class-remark, bpW:w3:coords, bpW:w3:flow, bpW:w1:torus-analytic
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:class-remark | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-an@L374-L374 | cited at this line (step; \ref{bpW:w3:class-remark})
EDGE: bpW:w3:coords | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-an@L375-L375 | cited at this line (step; \ref{bpW:w3:coords})
EDGE: bpW:w3:flow | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-an@L376-L376 | cited at this line (step; \ref{bpW:w3:flow})
EDGE: bpW:w1:torus-analytic | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-an@L376-L376 | cited at this line (step; \ref{bpW:w1:torus-analytic})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w6:to-w8
KIND: claim
TITLE: What W8 consumes from W6
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L383-L413
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L383-L413
CONTRACT_ID: bpW:w6:to-w8
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:initial, bpW:w6:exclusion, bpW:w7:measure, bpW:w7:shell-est, bpW:w6:freq-lip, bpW:w6:final-freq, bpW:w7:dioph, bpW:w7:limit, bpW:w6:tori, bpW:w6:wave-iteration, bpW:w6:applicable, bpW:w6:prep-step, bpW:w3:transport-tori-weak, bpW:w1:coordinatewise
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:initial | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L384-L384 | cited at this line (statement; \ref{bpW:w5:initial})
EDGE: bpW:w6:exclusion | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L387-L387 | cited at this line (statement; \ref{bpW:w6:exclusion})
EDGE: bpW:w7:measure | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L387-L387 | cited at this line (statement; \ref{bpW:w7:measure})
EDGE: bpW:w7:shell-est | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L388-L388 | cited at this line (statement; \ref{bpW:w7:shell-est})
EDGE: bpW:w6:freq-lip | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L388-L388 | cited at this line (statement; \ref{bpW:w6:freq-lip})
EDGE: bpW:w6:final-freq | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L390-L390 | cited at this line (statement; \ref{bpW:w6:final-freq})
EDGE: bpW:w7:dioph | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L390-L390 | cited at this line (statement; \ref{bpW:w7:dioph})
EDGE: bpW:w7:limit | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L390-L390 | cited at this line (statement; \ref{bpW:w7:limit})
EDGE: bpW:w6:tori | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L391-L391 | cited at this line (statement; \ref{bpW:w6:tori})
EDGE: bpW:w6:wave-iteration | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L396-L396 | cited at this line (statement; \ref{bpW:w6:wave-iteration})
EDGE: bpW:w6:applicable | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L396-L396 | cited at this line (statement; \ref{bpW:w6:applicable})
EDGE: bpW:w6:prep-step | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L398-L398 | cited at this line (statement; \ref{bpW:w6:prep-step})
EDGE: bpW:w3:transport-tori-weak | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L405-L405 | cited at this line (statement; \ref{bpW:w3:transport-tori-weak})
EDGE: bpW:w1:coordinatewise | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L407-L407 | cited at this line (statement; \ref{bpW:w1:coordinatewise})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: remark: its justification is inline (confirm, or exclude if not a mathematical claim)

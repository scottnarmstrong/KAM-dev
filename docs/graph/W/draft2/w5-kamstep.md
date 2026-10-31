NODE: bpW:w5:ext-taylor
KIND: external
TITLE: Taylor series in one complex variable, Banach values
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:ext-taylor@L46-L53
PROOF_SOURCE: -
CONTRACT_ID: bpW:w5:ext-taylor
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
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external item that cites \ref{bpW:w1:ext-onevar}: if it only restates the cited external, exclude it as an alias and point its consumers at the cited node (SPEC)

NODE: bpW:w5:ext-ftc
KIND: external
TITLE: Calculus along curves
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:ext-ftc@L54-L56
PROOF_SOURCE: -
CONTRACT_ID: bpW:w5:ext-ftc
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
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external item that cites \ref{bpW:w3:ext-integral}, \ref{bpW:w3:ext-neumann}, \ref{bpW:w1:ext-ode}: if it only restates the cited external, exclude it as an alias and point its consumers at the cited node (SPEC)

NODE: bpW:w5:setting
KIND: definition
TITLE: Phase space and symplectic form
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:setting@L62-L71
PROOF_SOURCE: -
CONTRACT_ID: bpW:w5:setting
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:kam-space, bpW:w4:index
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:kam-space | blueprint-W/parts/w5-kamstep.tex#bpW:w5:setting@L65-L65 | cited at this line (statement; \ref{bpW:w1:kam-space})
EDGE: bpW:w4:index | blueprint-W/parts/w5-kamstep.tex#bpW:w5:setting@L65-L65 | cited at this line (statement; \ref{bpW:w4:index})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w5:omega
KIND: lemma
TITLE: The form
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:omega@L75-L79
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:omega@L80-L88
CONTRACT_ID: bpW:w5:omega
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w5:ombd, stepW:w5:omnd, stepW:w5:omnorm
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w5:ombd | blueprint-W/parts/w5-kamstep.tex#bpW:w5:omega@L81-L81 | proof step of this result
EDGE: stepW:w5:omnd | blueprint-W/parts/w5-kamstep.tex#bpW:w5:omega@L83-L83 | proof step of this result
EDGE: stepW:w5:omnorm | blueprint-W/parts/w5-kamstep.tex#bpW:w5:omega@L86-L86 | proof step of this result
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:ombd
KIND: step
TITLE: Bound
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:ombd@L81-L82
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:ombd@L81-L82
CONTRACT_ID: stepW:w5:ombd
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
EDGE: bpW:w4:index | blueprint-W/parts/w5-kamstep.tex#stepW:w5:ombd@L82-L82 | cited at this line (step; \ref{bpW:w4:pairing})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:omnd
KIND: step
TITLE: Nondegeneracy
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:omnd@L83-L85
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:omnd@L83-L85
CONTRACT_ID: stepW:w5:omnd
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

NODE: stepW:w5:omnorm
KIND: step
TITLE: Norms
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:omnorm@L86-L87
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:omnorm@L86-L87
CONTRACT_ID: stepW:w5:omnorm
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:embed
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:embed | blueprint-W/parts/w5-kamstep.tex#stepW:w5:omnorm@L86-L86 | cited at this line (step; \ref{bpW:w1:embed})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w5:class
KIND: definition
TITLE: Smoothing Hamiltonians; parameter norms
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:class@L91-L105
PROOF_SOURCE: -
CONTRACT_ID: bpW:w5:class
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:holomorphic, bpW:w5:omega, bpW:w4:taylor
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:holomorphic | blueprint-W/parts/w5-kamstep.tex#bpW:w5:class@L93-L93 | cited at this line (statement; \ref{bpW:w1:holomorphic})
EDGE: bpW:w5:omega | blueprint-W/parts/w5-kamstep.tex#bpW:w5:class@L96-L96 | cited at this line (statement; \ref{bpW:w5:omega})
EDGE: bpW:w4:taylor | blueprint-W/parts/w5-kamstep.tex#bpW:w5:class@L97-L97 | cited at this line (statement; \ref{bpW:w4:taylor})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w5:lambda-product
KIND: claim
TITLE: Products
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:lambda-product@L109-L114
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:lambda-product@L109-L114
CONTRACT_ID: bpW:w5:lambda-product
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
NOTE: remark: its justification is inline (confirm, or exclude if not a mathematical claim)

NODE: bpW:w5:w4-general
KIND: lemma
TITLE: W4 with a general smoothing exponent
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-general@L123-L133
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-general@L134-L151
CONTRACT_ID: bpW:w5:w4-general
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w5:g-pair, stepW:w5:g-tail, stepW:w5:g-div, stepW:w5:g-diag, stepW:w5:g-rest, bpW:w4:ops, bpW:w4:taylor, bpW:w4:melnikov, bpW:w4:lie, bpW:w4:lemma1, bpW:w4:lemma2
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w5:g-pair | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-general@L136-L136 | proof step of this result
EDGE: stepW:w5:g-tail | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-general@L139-L139 | proof step of this result
EDGE: stepW:w5:g-div | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-general@L141-L141 | proof step of this result
EDGE: stepW:w5:g-diag | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-general@L144-L144 | proof step of this result
EDGE: stepW:w5:g-rest | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-general@L147-L147 | proof step of this result
EDGE: bpW:w4:ops | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-general@L124-L124 | cited at this line (statement; \ref{bpW:w4:ops})
EDGE: bpW:w4:taylor | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-general@L125-L125 | cited at this line (statement; \ref{bpW:w4:taylor})
EDGE: bpW:w4:melnikov | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-general@L125-L125 | cited at this line (statement; \ref{bpW:w4:freq})
EDGE: bpW:w4:lie | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-general@L130-L130 | cited at this line (statement; \ref{bpW:w4:lie})
EDGE: bpW:w4:lemma1 | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-general@L130-L130 | cited at this line (statement; \ref{bpW:w4:lemma1})
EDGE: bpW:w4:lemma2 | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-general@L130-L130 | cited at this line (statement; \ref{bpW:w4:lemma2})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:g-pair
KIND: step
TITLE: Pairings
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-pair@L136-L138
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-pair@L136-L138
CONTRACT_ID: stepW:w5:g-pair
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:index, bpW:w4:ops, bpW:w4:lie
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:index | blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-pair@L136-L136 | cited at this line (step; \ref{bpW:w4:pairing})
EDGE: bpW:w4:ops | blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-pair@L136-L136 | cited at this line (step; \ref{bpW:w4:ops})
EDGE: bpW:w4:lie | blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-pair@L137-L137 | cited at this line (step; \ref{bpW:w4:lie})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:g-tail
KIND: step
TITLE: Tails
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-tail@L139-L140
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-tail@L139-L140
CONTRACT_ID: stepW:w5:g-tail
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w4:liebd
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w4:liebd | blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-tail@L139-L139 | cited at this line (step; \ref{stepW:w4:liebd})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:g-div
KIND: step
TITLE: Divisors
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-div@L141-L143
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-div@L141-L143
CONTRACT_ID: stepW:w5:g-div
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w4:divlip
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w4:divlip | blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-div@L141-L141 | cited at this line (step; \ref{stepW:w4:divlip})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:g-diag
KIND: step
TITLE: Diagonals
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-diag@L144-L146
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-diag@L144-L146
CONTRACT_ID: stepW:w5:g-diag
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:schur, stepW:w4:Nhat
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:schur | blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-diag@L144-L144 | cited at this line (step; \ref{bpW:w4:schur})
EDGE: stepW:w4:Nhat | blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-diag@L145-L145 | cited at this line (step; \ref{stepW:w4:Nhat})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:g-rest
KIND: step
TITLE: Everything else
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-rest@L147-L150
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-rest@L147-L150
CONTRACT_ID: stepW:w5:g-rest
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:fourier-ops, bpW:w4:lattice, bpW:w4:schur, bpW:w4:solve, bpW:w4:extract, bpW:w4:components, bpW:w4:lemma1
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:fourier-ops | blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-rest@L147-L147 | cited at this line (step; \ref{bpW:w4:fourier-ops})
EDGE: bpW:w4:lattice | blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-rest@L147-L147 | cited at this line (step; \ref{bpW:w4:lattice})
EDGE: bpW:w4:schur | blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-rest@L148-L148 | cited at this line (step; \ref{bpW:w4:schur})
EDGE: bpW:w4:solve | blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-rest@L148-L148 | cited at this line (step; \ref{bpW:w4:solve})
EDGE: bpW:w4:extract | blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-rest@L148-L148 | cited at this line (step; \ref{bpW:w4:extract})
EDGE: bpW:w4:components | blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-rest@L148-L148 | cited at this line (step; \ref{bpW:w4:components})
EDGE: bpW:w4:lemma1 | blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-rest@L149-L149 | cited at this line (step; \ref{bpW:w4:lemma1})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w5:w4-modified
KIND: lemma
TITLE: Modified divisors for the preparatory step
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-modified@L156-L177
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-modified@L178-L222
CONTRACT_ID: bpW:w5:w4-modified
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w5:m-sup, stepW:w5:m-other, stepW:w5:m-lip, stepW:w5:m-act, stepW:w5:m-ass, stepW:w5:m-const, bpW:w5:w4-general, bpW:w4:melnikov, bpW:w4:lemma1
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w5:m-sup | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-modified@L180-L180 | proof step of this result
EDGE: stepW:w5:m-other | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-modified@L185-L185 | proof step of this result
EDGE: stepW:w5:m-lip | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-modified@L187-L187 | proof step of this result
EDGE: stepW:w5:m-act | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-modified@L191-L191 | proof step of this result
EDGE: stepW:w5:m-ass | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-modified@L213-L213 | proof step of this result
EDGE: stepW:w5:m-const | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-modified@L218-L218 | proof step of this result
EDGE: bpW:w5:w4-general | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-modified@L157-L157 | cited at this line (statement; \ref{bpW:w5:freq})
EDGE: bpW:w4:melnikov | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-modified@L158-L158 | cited at this line (statement; \ref{bpW:w4:melnikov})
EDGE: bpW:w4:lemma1 | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-modified@L163-L163 | cited at this line (statement; \ref{bpW:w4:lemma1})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:m-sup
KIND: step
TITLE: The $Q$-division
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-sup@L180-L184
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-sup@L180-L184
CONTRACT_ID: stepW:w5:m-sup
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:schur
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:schur | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-sup@L183-L183 | cited at this line (step; \ref{bpW:w4:schur})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:m-other
KIND: step
TITLE: Other components
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-other@L185-L186
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-other@L185-L186
CONTRACT_ID: stepW:w5:m-other
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

NODE: stepW:w5:m-lip
KIND: step
TITLE: Lipschitz
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-lip@L187-L190
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-lip@L187-L190
CONTRACT_ID: stepW:w5:m-lip
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w4:divlip, bpW:w4:solve, stepW:w4:lip
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w4:divlip | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-lip@L187-L187 | cited at this line (step; \ref{stepW:w4:divlip})
EDGE: bpW:w4:solve | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-lip@L190-L190 | cited at this line (step; \ref{bpW:w4:solve})
EDGE: stepW:w4:lip | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-lip@L190-L190 | cited at this line (step; \ref{stepW:w4:lip})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:m-act
KIND: step
TITLE: The action component
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-act@L191-L212
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-act@L191-L212
CONTRACT_ID: stepW:w5:m-act
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w4:Fcomp, bpW:w4:components, bpW:w4:w1-requests, stepW:w5:m-sup, bpW:w1:ext-unifderiv, bpW:w4:index, stepW:w4:assembly, stepW:w5:m-lip, bpW:w4:fourier-ops
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w4:Fcomp | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-act@L192-L192 | cited at this line (step; \ref{stepW:w4:Fcomp})
EDGE: bpW:w4:components | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-act@L195-L195 | cited at this line (step; \ref{bpW:w4:components})
EDGE: bpW:w4:w1-requests | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-act@L196-L196 | cited at this line (step; \ref{bpW:w4:F1})
EDGE: stepW:w5:m-sup | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-act@L196-L196 | cited at this line (step; \ref{stepW:w5:m-sup})
EDGE: bpW:w1:ext-unifderiv | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-act@L199-L199 | cited at this line (step; \ref{bpW:w1:ext-unifderiv})
EDGE: bpW:w4:index | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-act@L202-L202 | cited at this line (step; \ref{bpW:w4:pairing})
EDGE: stepW:w4:assembly | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-act@L204-L204 | cited at this line (step; \ref{stepW:w4:assembly})
EDGE: stepW:w5:m-lip | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-act@L206-L206 | cited at this line (step; \ref{stepW:w5:m-lip})
EDGE: bpW:w4:fourier-ops | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-act@L209-L209 | cited at this line (step; \ref{bpW:w4:fourier-ops})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:m-ass
KIND: step
TITLE: Assembly
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-ass@L213-L217
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-ass@L213-L217
CONTRACT_ID: stepW:w5:m-ass
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w4:Fcomp, stepW:w4:Nhat, stepW:w5:m-act, bpW:w4:lemma2
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w4:Fcomp | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-ass@L213-L213 | cited at this line (step; \ref{stepW:w4:Fcomp})
EDGE: stepW:w4:Nhat | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-ass@L213-L213 | cited at this line (step; \ref{stepW:w4:Nhat})
EDGE: stepW:w5:m-act | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-ass@L214-L214 | cited at this line (step; \ref{stepW:w5:m-act})
EDGE: bpW:w4:lemma2 | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-ass@L217-L217 | cited at this line (step; \ref{bpW:w4:lemma2})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:m-const
KIND: step
TITLE: The constant
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-const@L218-L221
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-const@L218-L221
CONTRACT_ID: stepW:w5:m-const
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:lattice
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:lattice | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-const@L220-L220 | cited at this line (step; \ref{bpW:w4:lattice})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w5:prep-gap
KIND: claim
TITLE: The exponents used by W6--W7
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:prep-gap@L240-L247
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:prep-gap@L240-L247
CONTRACT_ID: bpW:w5:prep-gap
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:constdef, bpW:w6:prep-step
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:constdef | blueprint-W/parts/w5-kamstep.tex#bpW:w5:prep-gap@L245-L245 | cited at this line (statement; \ref{bpW:w7:constdef})
EDGE: bpW:w6:prep-step | blueprint-W/parts/w5-kamstep.tex#bpW:w5:prep-gap@L246-L246 | cited at this line (statement; \ref{bpW:w6:prep-step})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: remark: its justification is inline (confirm, or exclude if not a mathematical claim)

NODE: bpW:w5:taylor
KIND: lemma
TITLE: Taylor approximation; P96-K (7)
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:taylor@L251-L271
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:taylor@L272-L306
CONTRACT_ID: bpW:w5:taylor
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w5:t-scale, stepW:w5:t-disc, stepW:w5:t-poly, stepW:w5:t-comp, stepW:w5:t-field, stepW:w5:t-est, bpW:w4:index
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w5:t-scale | blueprint-W/parts/w5-kamstep.tex#bpW:w5:taylor@L273-L273 | proof step of this result
EDGE: stepW:w5:t-disc | blueprint-W/parts/w5-kamstep.tex#bpW:w5:taylor@L277-L277 | proof step of this result
EDGE: stepW:w5:t-poly | blueprint-W/parts/w5-kamstep.tex#bpW:w5:taylor@L280-L280 | proof step of this result
EDGE: stepW:w5:t-comp | blueprint-W/parts/w5-kamstep.tex#bpW:w5:taylor@L285-L285 | proof step of this result
EDGE: stepW:w5:t-field | blueprint-W/parts/w5-kamstep.tex#bpW:w5:taylor@L293-L293 | proof step of this result
EDGE: stepW:w5:t-est | blueprint-W/parts/w5-kamstep.tex#bpW:w5:taylor@L299-L299 | proof step of this result
EDGE: bpW:w4:index | blueprint-W/parts/w5-kamstep.tex#bpW:w5:taylor@L261-L261 | cited at this line (statement; \ref{bpW:w4:index})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:t-scale
KIND: step
TITLE: Scaling identity
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-scale@L273-L276
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-scale@L273-L276
CONTRACT_ID: stepW:w5:t-scale
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

NODE: stepW:w5:t-disc
KIND: step
TITLE: Discs
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-disc@L277-L279
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-disc@L277-L279
CONTRACT_ID: stepW:w5:t-disc
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

NODE: stepW:w5:t-poly
KIND: step
TITLE: Taylor polynomial
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-poly@L280-L284
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-poly@L280-L284
CONTRACT_ID: stepW:w5:t-poly
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

NODE: stepW:w5:t-comp
KIND: step
TITLE: Components
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-comp@L285-L292
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-comp@L285-L292
CONTRACT_ID: stepW:w5:t-comp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:deriv-continuous, bpW:w1:cauchy, stepW:w5:t-est
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:deriv-continuous | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-comp@L287-L287 | cited at this line (step; \ref{bpW:w1:deriv-continuous})
EDGE: bpW:w1:cauchy | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-comp@L288-L288 | cited at this line (step; \ref{bpW:w1:cauchy})
EDGE: stepW:w5:t-est | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-comp@L289-L289 | cited at this line (step; \ref{stepW:w5:t-est})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:t-field
KIND: step
TITLE: Field
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-field@L293-L298
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-field@L293-L298
CONTRACT_ID: stepW:w5:t-field
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w5:t-scale
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w5:t-scale | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-field@L295-L295 | cited at this line (step; \ref{stepW:w5:t-scale})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:t-est
KIND: step
TITLE: Estimates
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-est@L299-L305
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-est@L299-L305
CONTRACT_ID: stepW:w5:t-est
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w5:t-disc, bpW:w5:ext-taylor, bpW:w5:omega
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w5:t-disc | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-est@L300-L300 | cited at this line (step; \ref{stepW:w5:t-disc})
EDGE: bpW:w5:ext-taylor | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-est@L301-L301 | cited at this line (step; \ref{bpW:w5:ext-taylor})
EDGE: bpW:w5:omega | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-est@L304-L304 | cited at this line (step; \ref{bpW:w5:omega})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w5:data
KIND: definition
TITLE: Step data
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:data@L313-L333
PROOF_SOURCE: -
CONTRACT_ID: bpW:w5:data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:choices, bpW:w5:w4-general, bpW:w4:melnikov, bpW:w5:w4-modified, bpW:w4:lemma1, bpW:w4:lattice
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:choices | blueprint-W/parts/w5-kamstep.tex#bpW:w5:data@L314-L314 | cited at this line (statement; \ref{bpW:w7:choices})
EDGE: bpW:w5:w4-general | blueprint-W/parts/w5-kamstep.tex#bpW:w5:data@L316-L316 | cited at this line (statement; \ref{bpW:w5:freq})
EDGE: bpW:w4:melnikov | blueprint-W/parts/w5-kamstep.tex#bpW:w5:data@L317-L317 | cited at this line (statement; \ref{bpW:w4:melnikov})
EDGE: bpW:w5:w4-modified | blueprint-W/parts/w5-kamstep.tex#bpW:w5:data@L318-L318 | cited at this line (statement; \ref{bpW:w5:w4-modified})
EDGE: bpW:w4:lemma1 | blueprint-W/parts/w5-kamstep.tex#bpW:w5:data@L324-L324 | cited at this line (statement; \ref{bpW:w4:lemma1})
EDGE: bpW:w4:lattice | blueprint-W/parts/w5-kamstep.tex#bpW:w5:data@L324-L324 | cited at this line (statement; \ref{bpW:w4:lattice})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w5:solve
KIND: lemma
TITLE: The solution of the homological equation in the step
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:solve@L337-L348
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:solve@L349-L361
CONTRACT_ID: bpW:w5:solve
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w5:s-in, stepW:w5:s-out, stepW:w5:s-class, bpW:w5:taylor, bpW:w4:lemma1, bpW:w5:w4-general, bpW:w5:w4-modified
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w5:s-in | blueprint-W/parts/w5-kamstep.tex#bpW:w5:solve@L350-L350 | proof step of this result
EDGE: stepW:w5:s-out | blueprint-W/parts/w5-kamstep.tex#bpW:w5:solve@L352-L352 | proof step of this result
EDGE: stepW:w5:s-class | blueprint-W/parts/w5-kamstep.tex#bpW:w5:solve@L357-L357 | proof step of this result
EDGE: bpW:w5:taylor | blueprint-W/parts/w5-kamstep.tex#bpW:w5:solve@L338-L338 | cited at this line (statement; \ref{bpW:w5:taylor})
EDGE: bpW:w4:lemma1 | blueprint-W/parts/w5-kamstep.tex#bpW:w5:solve@L339-L339 | cited at this line (statement; \ref{bpW:w4:lemma1})
EDGE: bpW:w5:w4-general | blueprint-W/parts/w5-kamstep.tex#bpW:w5:solve@L339-L339 | cited at this line (statement; \ref{bpW:w5:w4-general})
EDGE: bpW:w5:w4-modified | blueprint-W/parts/w5-kamstep.tex#bpW:w5:solve@L339-L339 | cited at this line (statement; \ref{bpW:w5:w4-modified})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:s-in
KIND: step
TITLE: Input
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:s-in@L350-L351
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:s-in@L350-L351
CONTRACT_ID: stepW:w5:s-in
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:taylor
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:taylor | blueprint-W/parts/w5-kamstep.tex#stepW:w5:s-in@L350-L350 | cited at this line (step; \ref{bpW:w5:taylor})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:s-out
KIND: step
TITLE: Output
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:s-out@L352-L356
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:s-out@L352-L356
CONTRACT_ID: stepW:w5:s-out
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:lemma2, bpW:w5:w4-general, bpW:w4:lattice, bpW:w4:lemma1, bpW:w4:lie
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:lemma2 | blueprint-W/parts/w5-kamstep.tex#stepW:w5:s-out@L352-L352 | cited at this line (step; \ref{bpW:w4:lemma2})
EDGE: bpW:w5:w4-general | blueprint-W/parts/w5-kamstep.tex#stepW:w5:s-out@L352-L352 | cited at this line (step; \ref{bpW:w5:w4-general})
EDGE: bpW:w4:lattice | blueprint-W/parts/w5-kamstep.tex#stepW:w5:s-out@L354-L354 | cited at this line (step; \ref{bpW:w4:lattice})
EDGE: bpW:w4:lemma1 | blueprint-W/parts/w5-kamstep.tex#stepW:w5:s-out@L355-L355 | cited at this line (step; \ref{bpW:w4:lemma1})
EDGE: bpW:w4:lie | blueprint-W/parts/w5-kamstep.tex#stepW:w5:s-out@L356-L356 | cited at this line (step; \ref{bpW:w4:lie})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:s-class
KIND: step
TITLE: Class
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:s-class@L357-L360
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:s-class@L357-L360
CONTRACT_ID: stepW:w5:s-class
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:holo-analytic-fd, bpW:w4:taylor
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:holo-analytic-fd | blueprint-W/parts/w5-kamstep.tex#stepW:w5:s-class@L358-L358 | cited at this line (step; \ref{bpW:w1:holo-analytic-fd})
EDGE: bpW:w4:taylor | blueprint-W/parts/w5-kamstep.tex#stepW:w5:s-class@L359-L359 | cited at this line (step; \ref{bpW:w4:taylor})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w5:flow
KIND: lemma
TITLE: The flow with explicit margins; P96-K (9)--(11) and Lemma~A.4
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow@L364-L379
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow@L380-L404
CONTRACT_ID: bpW:w5:flow
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w5:f-margin, stepW:w5:f-flow, stepW:w5:f-par, stepW:w5:f-der, stepW:w5:f-image, stepW:w5:f-real, bpW:w5:data, bpW:w1:flow
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w5:f-margin | blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow@L381-L381 | proof step of this result
EDGE: stepW:w5:f-flow | blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow@L384-L384 | proof step of this result
EDGE: stepW:w5:f-par | blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow@L388-L388 | proof step of this result
EDGE: stepW:w5:f-der | blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow@L394-L394 | proof step of this result
EDGE: stepW:w5:f-image | blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow@L398-L398 | proof step of this result
EDGE: stepW:w5:f-real | blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow@L400-L400 | proof step of this result
EDGE: bpW:w5:data | blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow@L365-L365 | cited at this line (statement; \ref{bpW:w5:small})
EDGE: bpW:w1:flow | blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow@L365-L365 | cited at this line (statement; \ref{bpW:w1:flow})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:f-margin
KIND: step
TITLE: Margins
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-margin@L381-L383
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-margin@L381-L383
CONTRACT_ID: stepW:w5:f-margin
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:kam-domain, bpW:w5:omega
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:kam-domain | blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-margin@L381-L381 | cited at this line (step; \ref{bpW:w1:kam-domain})
EDGE: bpW:w5:omega | blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-margin@L383-L383 | cited at this line (step; \ref{bpW:w5:omega})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:f-flow
KIND: step
TITLE: Flow
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-flow@L384-L387
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-flow@L384-L387
CONTRACT_ID: stepW:w5:f-flow
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:flow, bpW:w1:cauchy, bpW:w3:ext-integral
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:flow | blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-flow@L384-L384 | cited at this line (step; \ref{bpW:w1:flow})
EDGE: bpW:w1:cauchy | blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-flow@L387-L387 | cited at this line (step; \ref{bpW:w1:cauchy})
EDGE: bpW:w3:ext-integral | blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-flow@L387-L387 | cited at this line (step; \ref{bpW:w3:ext-integral})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:f-par
KIND: step
TITLE: Parameters
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-par@L388-L393
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-par@L388-L393
CONTRACT_ID: stepW:w5:f-par
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:flow, bpW:w1:cauchy
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:flow | blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-par@L388-L388 | cited at this line (step; \ref{bpW:w1:flow})
EDGE: bpW:w1:cauchy | blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-par@L392-L392 | cited at this line (step; \ref{bpW:w1:cauchy})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:f-der
KIND: step
TITLE: Derivative
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-der@L394-L397
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-der@L394-L397
CONTRACT_ID: stepW:w5:f-der
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:kam-domain, bpW:w1:cauchy, bpW:w5:data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:kam-domain | blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-der@L394-L394 | cited at this line (step; \ref{bpW:w1:kam-domain})
EDGE: bpW:w1:cauchy | blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-der@L396-L396 | cited at this line (step; \ref{bpW:w1:cauchy})
EDGE: bpW:w5:data | blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-der@L397-L397 | cited at this line (step; \ref{bpW:w5:small})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:f-image
KIND: step
TITLE: Image
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-image@L398-L399
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-image@L398-L399
CONTRACT_ID: stepW:w5:f-image
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

NODE: stepW:w5:f-real
KIND: step
TITLE: Reality and equivariance
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-real@L400-L403
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-real@L400-L403
CONTRACT_ID: stepW:w5:f-real
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:flow, bpW:w4:lemma1
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:flow | blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-real@L400-L400 | cited at this line (step; \ref{bpW:w1:flow})
EDGE: bpW:w4:lemma1 | blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-real@L401-L401 | cited at this line (step; \ref{bpW:w4:lemma1})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w5:flow-calc
KIND: lemma
TITLE: Flow calculus
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow-calc@L412-L425
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow-calc@L426-L448
CONTRACT_ID: bpW:w5:flow-calc
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w5:c-cont, stepW:w5:c-var, stepW:w5:c-skew, stepW:w5:c-symp, stepW:w5:c-inv, stepW:w5:c-trans, stepW:w5:c-time, bpW:w5:flow
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w5:c-cont | blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow-calc@L427-L427 | proof step of this result
EDGE: stepW:w5:c-var | blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow-calc@L431-L431 | proof step of this result
EDGE: stepW:w5:c-skew | blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow-calc@L434-L434 | proof step of this result
EDGE: stepW:w5:c-symp | blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow-calc@L437-L437 | proof step of this result
EDGE: stepW:w5:c-inv | blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow-calc@L439-L439 | proof step of this result
EDGE: stepW:w5:c-trans | blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow-calc@L441-L441 | proof step of this result
EDGE: stepW:w5:c-time | blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow-calc@L445-L445 | proof step of this result
EDGE: bpW:w5:flow | blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow-calc@L413-L413 | cited at this line (statement; \ref{bpW:w5:flow})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:c-cont
KIND: step
TITLE: Continuity
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-cont@L427-L430
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-cont@L427-L430
CONTRACT_ID: stepW:w5:c-cont
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:flow
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:flow | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-cont@L428-L428 | cited at this line (step; \ref{bpW:w1:flow})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:c-var
KIND: step
TITLE: Variational equation
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-var@L431-L433
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-var@L431-L433
CONTRACT_ID: stepW:w5:c-var
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:ext-integral, stepW:w5:c-cont, bpW:w1:deriv-continuous
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:ext-integral | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-var@L432-L432 | cited at this line (step; \ref{bpW:w3:ext-integral})
EDGE: stepW:w5:c-cont | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-var@L433-L433 | cited at this line (step; \ref{stepW:w5:c-cont})
EDGE: bpW:w1:deriv-continuous | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-var@L433-L433 | cited at this line (step; \ref{bpW:w1:deriv-continuous})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:c-skew
KIND: step
TITLE: Skewness
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-skew@L434-L436
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-skew@L434-L436
CONTRACT_ID: stepW:w5:c-skew
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w5:s-class
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w5:s-class | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-skew@L434-L434 | cited at this line (step; \ref{stepW:w5:s-class})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:c-symp
KIND: step
TITLE: Symplecticity
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-symp@L437-L438
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-symp@L437-L438
CONTRACT_ID: stepW:w5:c-symp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w5:c-var, stepW:w5:c-skew, bpW:w3:ext-mvt
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w5:c-var | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-symp@L438-L438 | cited at this line (step; \ref{stepW:w5:c-var})
EDGE: stepW:w5:c-skew | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-symp@L438-L438 | cited at this line (step; \ref{stepW:w5:c-skew})
EDGE: bpW:w3:ext-mvt | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-symp@L438-L438 | cited at this line (step; \ref{bpW:w3:ext-mvt})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:c-inv
KIND: step
TITLE: Inverse
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-inv@L439-L440
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-inv@L439-L440
CONTRACT_ID: stepW:w5:c-inv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:ext-neumann
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:ext-neumann | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-inv@L440-L440 | cited at this line (step; \ref{bpW:w3:ext-neumann})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:c-trans
KIND: step
TITLE: Transport
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-trans@L441-L444
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-trans@L441-L444
CONTRACT_ID: stepW:w5:c-trans
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:symplectic
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:symplectic | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-trans@L441-L441 | cited at this line (step; \ref{bpW:w3:symplectic})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w5:c-time
KIND: step
TITLE: Time derivative
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-time@L445-L447
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-time@L445-L447
CONTRACT_ID: stepW:w5:c-time
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:lie, bpW:w4:lemma1
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:lie | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-time@L447-L447 | cited at this line (step; \ref{bpW:w4:lie})
EDGE: bpW:w4:lemma1 | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-time@L447-L447 | cited at this line (step; \ref{bpW:w4:lemma1})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

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

NODE: bpW:w0n:recon-bounded
KIND: lemma
TITLE: Reconstruction is bounded into $C^k$
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:recon-bounded@L18-L27
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:recon-bounded@L29-L35
CONTRACT_ID: bpW:w0n:recon-bounded
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

NODE: bpW:w0n:quartic-coeff
KIND: lemma
TITLE: Closed form, (c)
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:quartic-coeff@L40-L51
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:quartic-coeff@L53-L69
CONTRACT_ID: bpW:w0n:quartic-coeff
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w0n:prod, stepW:w0n:cos, stepW:w0n:signed
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w0n:prod | blueprint-W/parts/w0-normalization.tex#bpW:w0n:quartic-coeff@L54-L54 | proof step of this result
EDGE: stepW:w0n:cos | blueprint-W/parts/w0-normalization.tex#bpW:w0n:quartic-coeff@L57-L57 | proof step of this result
EDGE: stepW:w0n:signed | blueprint-W/parts/w0-normalization.tex#bpW:w0n:quartic-coeff@L65-L65 | proof step of this result
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:prod
KIND: step
TITLE: Product to sum
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:prod@L54-L56
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:prod@L54-L56
CONTRACT_ID: stepW:w0n:prod
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

NODE: stepW:w0n:cos
KIND: step
TITLE: Cosine integrals
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:cos@L57-L64
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:cos@L57-L64
CONTRACT_ID: stepW:w0n:cos
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

NODE: stepW:w0n:signed
KIND: step
TITLE: Signed form
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:signed@L65-L68
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:signed@L65-L68
CONTRACT_ID: stepW:w0n:signed
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

NODE: bpW:w0n:gradient
KIND: lemma
TITLE: $G$ and its gradient as absolutely convergent sums
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:gradient@L76-L82
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:gradient@L84-L92
CONTRACT_ID: bpW:w0n:gradient
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:recon-bounded, bpW:w0:Gq#cubicGrad
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:recon-bounded | blueprint-W/parts/w0-normalization.tex#bpW:w0n:gradient@L85-L85 | cited at this line (proof; \ref{bpW:w0n:recon-bounded})
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w0-normalization.tex#bpW:w0n:gradient@L90-L90 | cited at this line (proof; \ref{bpW:w0:Gq})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w0n:algebra
KIND: lemma
TITLE: Weighted convolution algebra
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:algebra@L94-L98
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:algebra@L100-L113
CONTRACT_ID: bpW:w0n:algebra
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w0n:weight, stepW:w0n:young
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w0n:weight | blueprint-W/parts/w0-normalization.tex#bpW:w0n:algebra@L102-L102 | proof step of this result
EDGE: stepW:w0n:young | blueprint-W/parts/w0-normalization.tex#bpW:w0n:algebra@L107-L107 | proof step of this result
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:weight
KIND: step
TITLE: Weight inequality
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:weight@L102-L106
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:weight@L102-L106
CONTRACT_ID: stepW:w0n:weight
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

NODE: stepW:w0n:young
KIND: step
TITLE: Young and Cauchy--Schwarz
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:young@L107-L112
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:young@L107-L112
CONTRACT_ID: stepW:w0n:young
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

NODE: bpW:w0n:cubic-bound
KIND: theorem
TITLE: Cubic gradient, (b)
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L118-L129
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L131-L155
CONTRACT_ID: bpW:w0n:cubic-bound
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w0n:majorant, stepW:w0n:selection, stepW:w0n:smoothing, stepW:w0n:analytic, bpW:w0n:gradient
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w0n:majorant | blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L132-L132 | proof step of this result
EDGE: stepW:w0n:selection | blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L136-L136 | proof step of this result
EDGE: stepW:w0n:smoothing | blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L142-L142 | proof step of this result
EDGE: stepW:w0n:analytic | blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L149-L149 | proof step of this result
EDGE: bpW:w0n:gradient | blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L125-L125 | cited at this line (statement; \ref{bpW:w0n:gradient})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:majorant
KIND: step
TITLE: Even majorants
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:majorant@L132-L135
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:majorant@L132-L135
CONTRACT_ID: stepW:w0n:majorant
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

NODE: stepW:w0n:selection
KIND: step
TITLE: Selection rule bound
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:selection@L136-L141
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:selection@L136-L141
CONTRACT_ID: stepW:w0n:selection
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:quartic-coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w0-normalization.tex#stepW:w0n:selection@L137-L137 | cited at this line (step; \ref{bpW:w0n:g-signed})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:smoothing
KIND: step
TITLE: Smoothing
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:smoothing@L142-L148
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:smoothing@L142-L148
CONTRACT_ID: stepW:w0n:smoothing
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:algebra
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:algebra | blueprint-W/parts/w0-normalization.tex#stepW:w0n:smoothing@L146-L146 | cited at this line (step; \ref{bpW:w0n:algebra})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:analytic
KIND: step
TITLE: Analyticity
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:analytic@L149-L154
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:analytic@L149-L154
CONTRACT_ID: stepW:w0n:analytic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:gradient
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:gradient | blueprint-W/parts/w0-normalization.tex#stepW:w0n:analytic@L154-L154 | cited at this line (step; \ref{bpW:w0n:gradient})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w0n:pde-equiv
KIND: proposition
TITLE: Equivalence, (a)
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:pde-equiv@L165-L183
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:pde-equiv@L185-L209
CONTRACT_ID: bpW:w0n:pde-equiv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w0n:force, stepW:w0n:time, stepW:w0n:ident, stepW:w0n:converse, bpW:w0:eqmotion, bpW:w0:nlw#IsClassicalSolution
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w0n:force | blueprint-W/parts/w0-normalization.tex#bpW:w0n:pde-equiv@L186-L186 | proof step of this result
EDGE: stepW:w0n:time | blueprint-W/parts/w0-normalization.tex#bpW:w0n:pde-equiv@L193-L193 | proof step of this result
EDGE: stepW:w0n:ident | blueprint-W/parts/w0-normalization.tex#bpW:w0n:pde-equiv@L199-L199 | proof step of this result
EDGE: stepW:w0n:converse | blueprint-W/parts/w0-normalization.tex#bpW:w0n:pde-equiv@L202-L202 | proof step of this result
EDGE: bpW:w0:eqmotion | blueprint-W/parts/w0-normalization.tex#bpW:w0n:pde-equiv@L169-L169 | cited at this line (statement; \ref{bpW:w0:coeffsys})
EDGE: bpW:w0:nlw#IsClassicalSolution | blueprint-W/parts/w0-normalization.tex#bpW:w0n:pde-equiv@L170-L170 | cited at this line (statement; \ref{bpW:w0:eq})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:force
KIND: step
TITLE: Force identity
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:force@L186-L192
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:force@L186-L192
CONTRACT_ID: stepW:w0n:force
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:gradient, bpW:w0n:cubic-bound, bpW:w0n:recon-bounded
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:gradient | blueprint-W/parts/w0-normalization.tex#stepW:w0n:force@L187-L187 | cited at this line (step; \ref{bpW:w0n:gradient})
EDGE: bpW:w0n:cubic-bound | blueprint-W/parts/w0-normalization.tex#stepW:w0n:force@L188-L188 | cited at this line (step; \ref{bpW:w0n:cubic-bound})
EDGE: bpW:w0n:recon-bounded | blueprint-W/parts/w0-normalization.tex#stepW:w0n:force@L188-L188 | cited at this line (step; \ref{bpW:w0n:recon-bounded})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:time
KIND: step
TITLE: Time regularity
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:time@L193-L198
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:time@L193-L198
CONTRACT_ID: stepW:w0n:time
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

NODE: stepW:w0n:ident
KIND: step
TITLE: Identification
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:ident@L199-L201
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:ident@L199-L201
CONTRACT_ID: stepW:w0n:ident
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:recon-bounded
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:recon-bounded | blueprint-W/parts/w0-normalization.tex#stepW:w0n:ident@L201-L201 | cited at this line (step; \ref{bpW:w0n:recon-bounded})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:converse
KIND: step
TITLE: Converse
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:converse@L202-L208
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:converse@L202-L208
CONTRACT_ID: stepW:w0n:converse
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:gradient
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:gradient | blueprint-W/parts/w0-normalization.tex#stepW:w0n:converse@L207-L207 | cited at this line (step; \ref{bpW:w0n:gradient})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w0n:nonres
KIND: lemma
TITLE: Qualitative nonresonance of all quartic terms
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:nonres@L220-L224
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:nonres@L226-L247
CONTRACT_ID: bpW:w0n:nonres
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w0n:31, stepW:w0n:22, bpW:w0n:quartic-coeff
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w0n:31 | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nonres@L229-L229 | proof step of this result
EDGE: stepW:w0n:22 | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nonres@L233-L233 | proof step of this result
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nonres@L227-L227 | cited at this line (proof; \ref{bpW:w0n:quartic-coeff})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:31
KIND: step
TITLE: Four or three equal signs
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:31@L229-L232
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:31@L229-L232
CONTRACT_ID: stepW:w0n:31
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

NODE: stepW:w0n:22
KIND: step
TITLE: Two against two
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:22@L233-L246
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:22@L233-L246
CONTRACT_ID: stepW:w0n:22
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

NODE: bpW:w0n:nonres-remark
KIND: claim
TITLE: bpW:w0n:nonres-remark
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:nonres-remark@L248-L254
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:nonres-remark@L248-L254
CONTRACT_ID: bpW:w0n:nonres-remark
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

NODE: bpW:w0n:Qdef
KIND: definition
TITLE: Partial quartic normal form
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:Qdef@L270-L273
PROOF_SOURCE: -
CONTRACT_ID: bpW:w0n:Qdef
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

NODE: bpW:w0n:AB
KIND: theorem
TITLE: Action coefficients, (d)
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:AB@L275-L286
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:AB@L288-L305
CONTRACT_ID: bpW:w0n:AB
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w0n:resavg, stepW:w0n:moments, stepW:w0n:sum
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w0n:resavg | blueprint-W/parts/w0-normalization.tex#bpW:w0n:AB@L289-L289 | proof step of this result
EDGE: stepW:w0n:moments | blueprint-W/parts/w0-normalization.tex#bpW:w0n:AB@L295-L295 | proof step of this result
EDGE: stepW:w0n:sum | blueprint-W/parts/w0-normalization.tex#bpW:w0n:AB@L299-L299 | proof step of this result
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:resavg
KIND: step
TITLE: Resonant equals averaged
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:resavg@L289-L294
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:resavg@L289-L294
CONTRACT_ID: stepW:w0n:resavg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:nonres
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:nonres | blueprint-W/parts/w0-normalization.tex#stepW:w0n:resavg@L290-L290 | cited at this line (step; \ref{bpW:w0n:nonres})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:moments
KIND: step
TITLE: Averages of monomials
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:moments@L295-L298
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:moments@L295-L298
CONTRACT_ID: stepW:w0n:moments
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

NODE: stepW:w0n:sum
KIND: step
TITLE: Summation
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:sum@L299-L304
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:sum@L299-L304
CONTRACT_ID: stepW:w0n:sum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:quartic-coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w0-normalization.tex#stepW:w0n:sum@L300-L300 | cited at this line (step; \ref{bpW:w0n:quartic-coeff})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w0n:formal-birkhoff
KIND: proposition
TITLE: Formal partial Birkhoff transformation
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:formal-birkhoff@L307-L315
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:formal-birkhoff@L317-L323
CONTRACT_ID: bpW:w0n:formal-birkhoff
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:nonres
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:nonres | blueprint-W/parts/w0-normalization.tex#bpW:w0n:formal-birkhoff@L318-L318 | cited at this line (proof; \ref{bpW:w0n:nonres})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w0n:compare
KIND: claim
TITLE: Comparison with the printed coefficients
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:compare@L330-L337
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:compare@L330-L337
CONTRACT_ID: bpW:w0n:compare
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:harmless
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:harmless | blueprint-W/parts/w0-normalization.tex#bpW:w0n:compare@L336-L336 | cited at this line (statement; \ref{bpW:w0:harmless})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: remark: its justification is inline (confirm, or exclude if not a mathematical claim)

NODE: bpW:w0n:nondeg
KIND: theorem
TITLE: Nondegeneracy, (e)
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg@L346-L353
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg@L355-L377
CONTRACT_ID: bpW:w0n:nondeg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w0n:det, stepW:w0n:A2, stepW:w0n:A3red, stepW:w0n:l1, stepW:w0n:l2
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w0n:det | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg@L356-L356 | proof step of this result
EDGE: stepW:w0n:A2 | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg@L360-L360 | proof step of this result
EDGE: stepW:w0n:A3red | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg@L363-L363 | proof step of this result
EDGE: stepW:w0n:l1 | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg@L369-L369 | proof step of this result
EDGE: stepW:w0n:l2 | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg@L373-L373 | proof step of this result
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:det
KIND: step
TITLE: Determinant
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:det@L356-L359
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:det@L356-L359
CONTRACT_ID: stepW:w0n:det
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

NODE: stepW:w0n:A2
KIND: step
TITLE: Pure normal
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:A2@L360-L362
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:A2@L360-L362
CONTRACT_ID: stepW:w0n:A2
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

NODE: stepW:w0n:A3red
KIND: step
TITLE: Reduction of (A$_3$)
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:A3red@L363-L368
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:A3red@L363-L368
CONTRACT_ID: stepW:w0n:A3red
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

NODE: stepW:w0n:l1
KIND: step
TITLE: The case $\abs l=1$
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:l1@L369-L372
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:l1@L369-L372
CONTRACT_ID: stepW:w0n:l1
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

NODE: stepW:w0n:l2
KIND: step
TITLE: The case $\abs l=2$
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:l2@L373-L376
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:l2@L373-L376
CONTRACT_ID: stepW:w0n:l2
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

NODE: bpW:w0n:kappa
KIND: claim
TITLE: Spectral asymptotics with the corrected $B$
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:kappa@L383-L387
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:kappa@L383-L387
CONTRACT_ID: bpW:w0n:kappa
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

NODE: bpW:w0n:duffing
KIND: proposition
TITLE: One-mode frequency shift, (f)
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:duffing@L391-L400
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:duffing@L402-L407
CONTRACT_ID: bpW:w0n:duffing
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:nlw#IsClassicalSolution
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:nlw#IsClassicalSolution | blueprint-W/parts/w0-normalization.tex#bpW:w0n:duffing@L392-L392 | cited at this line (statement; \ref{bpW:w0:eq})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

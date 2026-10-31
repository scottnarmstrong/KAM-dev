NODE: bpW:w2:ext-deriv
KIND: external
TITLE: One-variable calculus
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:ext-deriv@L40-L48
PROOF_SOURCE: -
CONTRACT_ID: bpW:w2:ext-deriv
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
NOTE: -

NODE: bpW:w2:ext-an
KIND: external
TITLE: Analytic maps on $\R\times\R$
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:ext-an@L49-L54
PROOF_SOURCE: -
CONTRACT_ID: bpW:w2:ext-an
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
NOTE: -

NODE: bpW:w2:ext-sums
KIND: external
TITLE: Series and norms
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:ext-sums@L55-L60
PROOF_SOURCE: -
CONTRACT_ID: bpW:w2:ext-sums
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
NOTE: -

NODE: bpW:w2:ext-trig
KIND: external
TITLE: Trigonometry
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:ext-trig@L61-L64
PROOF_SOURCE: -
CONTRACT_ID: bpW:w2:ext-trig
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
NOTE: -

NODE: bpW:w2:derived
KIND: definition
TITLE: Derived reconstructions
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:derived@L70-L76
PROOF_SOURCE: -
CONTRACT_ID: bpW:w2:derived
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

NODE: bpW:w2:functionals
KIND: lemma
TITLE: Reconstruction functionals
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:functionals@L81-L92
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:functionals@L94-L124
CONTRACT_ID: bpW:w2:functionals
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w2:features, stepW:w2:pairing, stepW:w2:norms, stepW:w2:xder, stepW:w2:bdry
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w2:features | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:functionals@L95-L95 | proof step of this result
EDGE: stepW:w2:pairing | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:functionals@L103-L103 | proof step of this result
EDGE: stepW:w2:norms | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:functionals@L108-L108 | proof step of this result
EDGE: stepW:w2:xder | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:functionals@L114-L114 | proof step of this result
EDGE: stepW:w2:bdry | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:functionals@L120-L120 | proof step of this result
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:features
KIND: step
TITLE: Choice of the features
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:features@L95-L102
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:features@L95-L102
CONTRACT_ID: stepW:w2:features
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:sine-feature
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:sine-feature | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:features@L96-L96 | cited at this line (step; \ref{bpW:w1:sine-feature})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:pairing
KIND: step
TITLE: Pairings
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:pairing@L103-L107
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:pairing@L103-L107
CONTRACT_ID: stepW:w2:pairing
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:sine-feature, bpW:w2:derived, bpW:w2:ext-sums
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:sine-feature | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:pairing@L104-L104 | cited at this line (step; \ref{bpW:w1:sine-feature})
EDGE: bpW:w2:derived | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:pairing@L106-L106 | cited at this line (step; \ref{bpW:w2:derived})
EDGE: bpW:w2:ext-sums | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:pairing@L107-L107 | cited at this line (step; \ref{bpW:w2:ext-sums})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:norms
KIND: step
TITLE: Norms
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:norms@L108-L113
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:norms@L108-L113
CONTRACT_ID: stepW:w2:norms
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-lp, bpW:w2:ext-sums
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-lp | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:norms@L113-L113 | cited at this line (step; \ref{bpW:w1:ext-lp})
EDGE: bpW:w2:ext-sums | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:norms@L113-L113 | cited at this line (step; \ref{bpW:w2:ext-sums})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:xder
KIND: step
TITLE: $x$-derivatives
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:xder@L114-L119
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:xder@L114-L119
CONTRACT_ID: stepW:w2:xder
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:recder, bpW:w1:recon-analytic, bpW:w2:ext-trig, bpW:w2:ext-deriv
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:recder | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:xder@L115-L115 | cited at this line (step; \ref{stepW:w1:recder})
EDGE: bpW:w1:recon-analytic | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:xder@L115-L115 | cited at this line (step; \ref{bpW:w1:recon-analytic})
EDGE: bpW:w2:ext-trig | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:xder@L116-L116 | cited at this line (step; \ref{bpW:w2:ext-trig})
EDGE: bpW:w2:ext-deriv | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:xder@L119-L119 | cited at this line (step; \ref{bpW:w2:ext-deriv})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:bdry
KIND: step
TITLE: Boundary values
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bdry@L120-L123
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bdry@L120-L123
CONTRACT_ID: stepW:w2:bdry
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:ext-trig
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:ext-trig | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bdry@L121-L121 | cited at this line (step; \ref{bpW:w2:ext-trig})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w2:force
KIND: lemma
TITLE: Force identity in frozen form
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L128-L137
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L139-L160
CONTRACT_ID: bpW:w2:force
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w2:fsum, stepW:w2:flin, stepW:w2:fcub
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w2:fsum | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L140-L140 | proof step of this result
EDGE: stepW:w2:flin | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L148-L148 | proof step of this result
EDGE: stepW:w2:fcub | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L154-L154 | proof step of this result
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:fsum
KIND: step
TITLE: Summability
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L140-L147
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L140-L147
CONTRACT_ID: stepW:w2:fsum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-lp, bpW:w1:cubic-analytic, bpW:w2:ext-sums, bpW:w2:functionals
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-lp | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L141-L141 | cited at this line (step; \ref{bpW:w1:ext-lp})
EDGE: bpW:w1:cubic-analytic | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L143-L143 | cited at this line (step; \ref{bpW:w1:cubic-analytic})
EDGE: bpW:w2:ext-sums | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L146-L146 | cited at this line (step; \ref{bpW:w2:ext-sums})
EDGE: bpW:w2:functionals | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L147-L147 | cited at this line (step; \ref{bpW:w2:functionals})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:flin
KIND: step
TITLE: Linear part
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:flin@L148-L153
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:flin@L148-L153
CONTRACT_ID: stepW:w2:flin
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:ext-trig, bpW:w0n:pde-equiv
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:ext-trig | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:flin@L149-L149 | cited at this line (step; \ref{bpW:w2:ext-trig})
EDGE: bpW:w0n:pde-equiv | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:flin@L153-L153 | cited at this line (step; \ref{bpW:w0n:force})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:fcub
KIND: step
TITLE: Cubic part
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L154-L159
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L154-L159
CONTRACT_ID: stepW:w2:fcub
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:trifrozen, bpW:w1:trilinear, bpW:w0:reconstruction#reconU, bpW:w0:reconstruction#reconV, bpW:w0:Gq#cubicGrad, bpW:w0n:pde-equiv, stepW:w0n:force, bpW:w1:sine-completeness
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:trifrozen | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L155-L155 | cited at this line (step; \ref{stepW:w1:trifrozen})
EDGE: bpW:w1:trilinear | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L155-L155 | cited at this line (step; \ref{bpW:w1:trilinear})
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L156-L156 | cited at this line (step; \ref{bpW:w0:reconstruction})
EDGE: bpW:w0:reconstruction#reconV | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L156-L156 | cited at this line (step; \ref{bpW:w0:reconstruction})
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L157-L157 | cited at this line (step; \ref{bpW:w0:Gq})
EDGE: bpW:w0n:pde-equiv | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L157-L157 | cited at this line (step; \ref{bpW:w0n:force})
EDGE: stepW:w0n:force | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L157-L157 | cited at this line (step; \ref{stepW:w0n:force})
EDGE: bpW:w1:sine-completeness | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L158-L158 | cited at this line (step; \ref{bpW:w1:sine-completeness})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w2:coeffsol
KIND: definition
TITLE: Analytic coefficient solution
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:coeffsol@L166-L174
PROOF_SOURCE: -
CONTRACT_ID: bpW:w2:coeffsol
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

NODE: bpW:w2:orbit
KIND: lemma
TITLE: Torus orbits are analytic coefficient solutions
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:orbit@L178-L190
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:orbit@L192-L202
CONTRACT_ID: bpW:w2:orbit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w2:oan, stepW:w2:oshift
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w2:oan | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:orbit@L193-L193 | proof step of this result
EDGE: stepW:w2:oshift | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:orbit@L196-L196 | proof step of this result
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:oan
KIND: step
TITLE: Analyticity
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:oan@L193-L195
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:oan@L193-L195
CONTRACT_ID: stepW:w2:oan
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:ext-an
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:ext-an | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:oan@L195-L195 | cited at this line (step; \ref{bpW:w2:ext-an})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:oshift
KIND: step
TITLE: Shift
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:oshift@L196-L201
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:oshift@L196-L201
CONTRACT_ID: stepW:w2:oshift
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:ext-deriv
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:ext-deriv | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:oshift@L198-L198 | cited at this line (step; \ref{bpW:w2:ext-deriv})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w2:curve-deriv
KIND: lemma
TITLE: Coefficients of the curve derivative
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve-deriv@L206-L210
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve-deriv@L212-L220
CONTRACT_ID: bpW:w2:curve-deriv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w2:cdiff, stepW:w2:ccoord
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w2:cdiff | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve-deriv@L213-L213 | proof step of this result
EDGE: stepW:w2:ccoord | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve-deriv@L216-L216 | proof step of this result
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:cdiff
KIND: step
TITLE: Differentiability
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:cdiff@L213-L215
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:cdiff@L213-L215
CONTRACT_ID: stepW:w2:cdiff
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:ext-an
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:ext-an | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:cdiff@L215-L215 | cited at this line (step; \ref{bpW:w2:ext-an})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:ccoord
KIND: step
TITLE: Coordinates
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:ccoord@L216-L219
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:ccoord@L216-L219
CONTRACT_ID: stepW:w2:ccoord
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:coordinatewise, bpW:w2:coeffsol, bpW:w2:ext-deriv
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:coordinatewise | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:ccoord@L217-L217 | cited at this line (step; \ref{bpW:w1:coordinatewise})
EDGE: bpW:w2:coeffsol | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:ccoord@L218-L218 | cited at this line (step; \ref{bpW:w2:C2})
EDGE: bpW:w2:ext-deriv | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:ccoord@L219-L219 | cited at this line (step; \ref{bpW:w2:ext-deriv})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w2:hidden
KIND: claim
TITLE: Regularity hidden in the hypotheses
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:hidden@L223-L229
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:hidden@L223-L229
CONTRACT_ID: bpW:w2:hidden
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:curve-deriv, bpW:w1:coordinatewise, bpW:w1:hamfield
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:curve-deriv | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:hidden@L224-L224 | cited at this line (statement; \ref{bpW:w2:curve-deriv})
EDGE: bpW:w1:coordinatewise | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:hidden@L227-L227 | cited at this line (statement; \ref{bpW:w1:coordinatewise})
EDGE: bpW:w1:hamfield | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:hidden@L228-L228 | cited at this line (statement; \ref{bpW:w1:hamfield})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: remark: its justification is inline (confirm, or exclude if not a mathematical claim)

NODE: bpW:w2:curve
KIND: theorem
TITLE: P96-W Lemma~1 in frozen form
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L233-L249
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L251-L296
CONTRACT_ID: bpW:w2:curve
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w2:joint, stepW:w2:t1, stepW:w2:t2, stepW:w2:x, stepW:w2:frozen, stepW:w2:bound, bpW:w2:functionals
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w2:joint | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L252-L252 | proof step of this result
EDGE: stepW:w2:t1 | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L263-L263 | proof step of this result
EDGE: stepW:w2:t2 | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L271-L271 | proof step of this result
EDGE: stepW:w2:x | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L279-L279 | proof step of this result
EDGE: stepW:w2:frozen | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L281-L281 | proof step of this result
EDGE: stepW:w2:bound | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L290-L290 | proof step of this result
EDGE: bpW:w2:functionals | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L238-L238 | cited at this line (statement; \ref{bpW:w2:functionals})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:joint
KIND: step
TITLE: Joint analyticity
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:joint@L252-L262
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:joint@L252-L262
CONTRACT_ID: stepW:w2:joint
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w2:cdiff, bpW:w1:recon-analytic, bpW:w2:ext-an, bpW:w1:ext-analytic, bpW:w2:functionals
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w2:cdiff | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:joint@L253-L253 | cited at this line (step; \ref{stepW:w2:cdiff})
EDGE: bpW:w1:recon-analytic | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:joint@L253-L253 | cited at this line (step; \ref{bpW:w1:recon-analytic})
EDGE: bpW:w2:ext-an | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:joint@L257-L257 | cited at this line (step; \ref{bpW:w2:ext-an})
EDGE: bpW:w1:ext-analytic | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:joint@L259-L259 | cited at this line (step; \ref{bpW:w1:ext-analytic})
EDGE: bpW:w2:functionals | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:joint@L259-L259 | cited at this line (step; \ref{bpW:w2:functionals})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:t1
KIND: step
TITLE: First time derivative
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L263-L270
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L263-L270
CONTRACT_ID: stepW:w2:t1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:functionals, bpW:w2:ext-deriv, bpW:w2:curve-deriv, bpW:w2:ext-trig
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:functionals | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L265-L265 | cited at this line (step; \ref{bpW:w2:functionals})
EDGE: bpW:w2:ext-deriv | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L266-L266 | cited at this line (step; \ref{bpW:w2:ext-deriv})
EDGE: bpW:w2:curve-deriv | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L267-L267 | cited at this line (step; \ref{bpW:w2:curve-deriv})
EDGE: bpW:w2:ext-trig | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L267-L267 | cited at this line (step; \ref{bpW:w2:ext-trig})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:t2
KIND: step
TITLE: Second time derivative
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L271-L278
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L271-L278
CONTRACT_ID: stepW:w2:t2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:curve-deriv, bpW:w2:force, stepW:w2:fsum
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:curve-deriv | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L273-L273 | cited at this line (step; \ref{bpW:w2:curve-deriv})
EDGE: bpW:w2:force | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L275-L275 | cited at this line (step; \ref{bpW:w2:force})
EDGE: stepW:w2:fsum | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L275-L275 | cited at this line (step; \ref{stepW:w2:fsum})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:x
KIND: step
TITLE: Space derivatives
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:x@L279-L280
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:x@L279-L280
CONTRACT_ID: stepW:w2:x
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:functionals
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:functionals | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:x@L280-L280 | cited at this line (step; \ref{bpW:w2:functionals})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:frozen
KIND: step
TITLE: The frozen definition
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:frozen@L281-L289
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:frozen@L281-L289
CONTRACT_ID: stepW:w2:frozen
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w2:joint, bpW:w2:ext-an, bpW:w2:functionals
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w2:joint | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:frozen@L283-L283 | cited at this line (step; \ref{stepW:w2:joint})
EDGE: bpW:w2:ext-an | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:frozen@L283-L283 | cited at this line (step; \ref{bpW:w2:ext-an})
EDGE: bpW:w2:functionals | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:frozen@L289-L289 | cited at this line (step; \ref{bpW:w2:functionals})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:bound
KIND: step
TITLE: Bound
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bound@L290-L295
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bound@L290-L295
CONTRACT_ID: stepW:w2:bound
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w2:frozen, bpW:w2:ext-deriv, bpW:w2:functionals, bpW:w2:ext-sums
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w2:frozen | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bound@L291-L291 | cited at this line (step; \ref{stepW:w2:frozen})
EDGE: bpW:w2:ext-deriv | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bound@L292-L292 | cited at this line (step; \ref{bpW:w2:ext-deriv})
EDGE: bpW:w2:functionals | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bound@L293-L293 | cited at this line (step; \ref{bpW:w2:functionals})
EDGE: bpW:w2:ext-sums | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bound@L295-L295 | cited at this line (step; \ref{bpW:w2:ext-sums})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w2:main
KIND: theorem
TITLE: PDE solutions on invariant tori
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:main@L303-L321
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:main@L323-L332
CONTRACT_ID: bpW:w2:main
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w2:mred, stepW:w2:mconc, bpW:w2:curve, bpW:w2:orbit
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w2:mred | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:main@L324-L324 | proof step of this result
EDGE: stepW:w2:mconc | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:main@L328-L328 | proof step of this result
EDGE: bpW:w2:curve | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:main@L304-L304 | cited at this line (statement; \ref{bpW:w2:curve})
EDGE: bpW:w2:orbit | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:main@L308-L308 | cited at this line (statement; \ref{bpW:w2:inv})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:mred
KIND: step
TITLE: Reduction to a curve
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:mred@L324-L327
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:mred@L324-L327
CONTRACT_ID: stepW:w2:mred
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:orbit, bpW:w2:curve
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:orbit | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:mred@L326-L326 | cited at this line (step; \ref{bpW:w2:orbit})
EDGE: bpW:w2:curve | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:mred@L327-L327 | cited at this line (step; \ref{bpW:w2:curve})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:mconc
KIND: step
TITLE: Conclusions
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:mconc@L328-L331
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:mconc@L328-L331
CONTRACT_ID: stepW:w2:mconc
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:curve
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:curve | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:mconc@L329-L329 | cited at this line (step; \ref{bpW:w2:curve})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w2:hyp
KIND: claim
TITLE: Hypotheses
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:hyp@L336-L345
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:hyp@L336-L345
CONTRACT_ID: bpW:w2:hyp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:main, bpW:w1:torus-analytic, bpW:w2:orbit, bpW:w2:curve
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:main | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:hyp@L337-L337 | cited at this line (statement; \ref{bpW:w2:H1})
EDGE: bpW:w1:torus-analytic | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:hyp@L341-L341 | cited at this line (statement; \ref{bpW:w1:torus-analytic})
EDGE: bpW:w2:orbit | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:hyp@L342-L342 | cited at this line (statement; \ref{bpW:w2:orbit})
EDGE: bpW:w2:curve | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:hyp@L342-L342 | cited at this line (statement; \ref{bpW:w2:curve})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: remark: its justification is inline (confirm, or exclude if not a mathematical claim)

NODE: bpW:w2:clause5
KIND: corollary
TITLE: Clause (5) with the common constant
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:clause5@L347-L353
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:clause5@L355-L360
CONTRACT_ID: bpW:w2:clause5
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:main
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:main | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:clause5@L358-L358 | cited at this line (proof; \ref{bpW:w2:main})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w2:constants
KIND: claim
TITLE: Order of constants
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:constants@L363-L371
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:constants@L363-L371
CONTRACT_ID: bpW:w2:constants
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w2:norms
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w2:norms | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:constants@L369-L369 | cited at this line (statement; \ref{stepW:w2:norms})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: remark: its justification is inline (confirm, or exclude if not a mathematical claim)

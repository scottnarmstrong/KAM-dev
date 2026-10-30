NODE: bpW:w1:sine-completeness
KIND: lemma
TITLE: Completeness of the sine system
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-completeness@L593-L596
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-completeness@L598-L613
CONTRACT_ID: bpW:w1:sine-completeness
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:odd, stepW:w1:coeffs, stepW:w1:basis, stepW:w1:cont
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:odd | blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-completeness@L599-L599 | proof step of this result
EDGE: stepW:w1:coeffs | blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-completeness@L602-L602 | proof step of this result
EDGE: stepW:w1:basis | blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-completeness@L606-L606 | proof step of this result
EDGE: stepW:w1:cont | blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-completeness@L610-L610 | proof step of this result
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:odd
KIND: step
TITLE: Odd extension
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:odd@L599-L601
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:odd@L599-L601
CONTRACT_ID: stepW:w1:odd
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

NODE: stepW:w1:coeffs
KIND: step
TITLE: Fourier coefficients vanish
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:coeffs@L602-L605
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:coeffs@L602-L605
CONTRACT_ID: stepW:w1:coeffs
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

NODE: stepW:w1:basis
KIND: step
TITLE: Hilbert basis
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:basis@L606-L609
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:basis@L606-L609
CONTRACT_ID: stepW:w1:basis
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-fourier
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-fourier | blueprint-W/parts/w1-sequences.tex#stepW:w1:basis@L608-L608 | cited at this line (step; \ref{bpW:w1:ext-fourier})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:cont
KIND: step
TITLE: Continuity
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:cont@L610-L612
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:cont@L610-L612
CONTRACT_ID: stepW:w1:cont
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

NODE: bpW:w1:sine-feature
KIND: lemma
TITLE: Analytic sine features
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-feature@L617-L629
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-feature@L631-L645
CONTRACT_ID: bpW:w1:sine-feature
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:growth, stepW:w1:normal, stepW:w1:sinereal
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:growth | blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-feature@L632-L632 | proof step of this result
EDGE: stepW:w1:normal | blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-feature@L636-L636 | proof step of this result
EDGE: stepW:w1:sinereal | blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-feature@L641-L641 | proof step of this result
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:growth
KIND: step
TITLE: Growth on the strip
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:growth@L632-L635
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:growth@L632-L635
CONTRACT_ID: stepW:w1:growth
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

NODE: stepW:w1:normal
KIND: step
TITLE: Normal convergence
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:normal@L636-L640
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:normal@L636-L640
CONTRACT_ID: stepW:w1:normal
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-onevar
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-onevar | blueprint-W/parts/w1-sequences.tex#stepW:w1:normal@L640-L640 | cited at this line (step; \ref{bpW:w1:ext-onevar})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:sinereal
KIND: step
TITLE: Real restriction
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:sinereal@L641-L644
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:sinereal@L641-L644
CONTRACT_ID: stepW:w1:sinereal
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:complexification-lemma
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:complexification-lemma | blueprint-W/parts/w1-sequences.tex#stepW:w1:sinereal@L643-L643 | cited at this line (step; \ref{bpW:w1:complexification-lemma})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:recon-analytic
KIND: corollary
TITLE: Analytic reconstruction
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:recon-analytic@L648-L670
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:recon-analytic@L672-L692
CONTRACT_ID: bpW:w1:recon-analytic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:bil, stepW:w1:recanalytic, stepW:w1:recder, bpW:w1:sine-feature
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:bil | blueprint-W/parts/w1-sequences.tex#bpW:w1:recon-analytic@L673-L673 | proof step of this result
EDGE: stepW:w1:recanalytic | blueprint-W/parts/w1-sequences.tex#bpW:w1:recon-analytic@L677-L677 | proof step of this result
EDGE: stepW:w1:recder | blueprint-W/parts/w1-sequences.tex#bpW:w1:recon-analytic@L683-L683 | proof step of this result
EDGE: bpW:w1:sine-feature | blueprint-W/parts/w1-sequences.tex#bpW:w1:recon-analytic@L650-L650 | cited at this line (statement; \ref{bpW:w1:sine-feature})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:bil
KIND: step
TITLE: Bilinear form
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:bil@L673-L676
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:bil@L673-L676
CONTRACT_ID: stepW:w1:bil
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
EDGE: bpW:w1:sine-feature | blueprint-W/parts/w1-sequences.tex#stepW:w1:bil@L674-L674 | cited at this line (step; \ref{bpW:w1:sine-feature})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:recanalytic
KIND: step
TITLE: Analyticity
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:recanalytic@L677-L682
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:recanalytic@L677-L682
CONTRACT_ID: stepW:w1:recanalytic
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

NODE: stepW:w1:recder
KIND: step
TITLE: Derivatives
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:recder@L683-L691
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:recder@L683-L691
CONTRACT_ID: stepW:w1:recder
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

NODE: bpW:w1:complexification
KIND: definition
TITLE: Complexification
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:complexification@L698-L703
PROOF_SOURCE: -
CONTRACT_ID: bpW:w1:complexification
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

NODE: bpW:w1:complexification-lemma
KIND: lemma
TITLE: Complexification and real analyticity
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:complexification-lemma@L707-L718
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:complexification-lemma@L720-L725
CONTRACT_ID: bpW:w1:complexification-lemma
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-analytic
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-analytic | blueprint-W/parts/w1-sequences.tex#bpW:w1:complexification-lemma@L722-L722 | cited at this line (proof; \ref{bpW:w1:ext-analytic})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:holomorphic
KIND: definition
TITLE: Holomorphic maps on Banach domains
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:holomorphic@L728-L734
PROOF_SOURCE: -
CONTRACT_ID: bpW:w1:holomorphic
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

NODE: bpW:w1:cauchy
KIND: lemma
TITLE: Cauchy estimate
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:cauchy@L737-L742
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:cauchy@L744-L752
CONTRACT_ID: bpW:w1:cauchy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:lines, stepW:w1:onevar, stepW:w1:margins
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:lines | blueprint-W/parts/w1-sequences.tex#bpW:w1:cauchy@L745-L745 | proof step of this result
EDGE: stepW:w1:onevar | blueprint-W/parts/w1-sequences.tex#bpW:w1:cauchy@L748-L748 | proof step of this result
EDGE: stepW:w1:margins | blueprint-W/parts/w1-sequences.tex#bpW:w1:cauchy@L750-L750 | proof step of this result
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:lines
KIND: step
TITLE: Complex lines
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:lines@L745-L747
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:lines@L745-L747
CONTRACT_ID: stepW:w1:lines
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

NODE: stepW:w1:onevar
KIND: step
TITLE: One-variable estimate
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:onevar@L748-L749
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:onevar@L748-L749
CONTRACT_ID: stepW:w1:onevar
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-onevar
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-onevar | blueprint-W/parts/w1-sequences.tex#stepW:w1:onevar@L749-L749 | cited at this line (step; \ref{bpW:w1:ext-onevar})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:margins
KIND: step
TITLE: Margins
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:margins@L750-L751
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:margins@L750-L751
CONTRACT_ID: stepW:w1:margins
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-unifderiv
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-unifderiv | blueprint-W/parts/w1-sequences.tex#stepW:w1:margins@L751-L751 | cited at this line (step; \ref{bpW:w1:ext-unifderiv})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:deriv-continuous
KIND: lemma
TITLE: Derivatives of holomorphic maps are continuous
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:deriv-continuous@L755-L760
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:deriv-continuous@L762-L775
CONTRACT_ID: bpW:w1:deriv-continuous
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:dcbound, stepW:w1:dcintegral, stepW:w1:dclip
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:dcbound | blueprint-W/parts/w1-sequences.tex#bpW:w1:deriv-continuous@L763-L763 | proof step of this result
EDGE: stepW:w1:dcintegral | blueprint-W/parts/w1-sequences.tex#bpW:w1:deriv-continuous@L765-L765 | proof step of this result
EDGE: stepW:w1:dclip | blueprint-W/parts/w1-sequences.tex#bpW:w1:deriv-continuous@L769-L769 | proof step of this result
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:dcbound
KIND: step
TITLE: Existence of $\rho$, $B$
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:dcbound@L763-L764
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:dcbound@L763-L764
CONTRACT_ID: stepW:w1:dcbound
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

NODE: stepW:w1:dcintegral
KIND: step
TITLE: Cauchy integral along lines
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:dcintegral@L765-L768
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:dcintegral@L765-L768
CONTRACT_ID: stepW:w1:dcintegral
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-onevar
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-onevar | blueprint-W/parts/w1-sequences.tex#stepW:w1:dcintegral@L767-L767 | cited at this line (step; \ref{bpW:w1:ext-onevar})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:dclip
KIND: step
TITLE: Lipschitz difference
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:dclip@L769-L774
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:dclip@L769-L774
CONTRACT_ID: stepW:w1:dclip
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
EDGE: bpW:w1:cauchy | blueprint-W/parts/w1-sequences.tex#stepW:w1:dclip@L771-L771 | cited at this line (step; \ref{bpW:w1:cauchy})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:uniform-limit
KIND: lemma
TITLE: Uniform limits
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:uniform-limit@L778-L786
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:uniform-limit@L788-L798
CONTRACT_ID: bpW:w1:uniform-limit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:ulcauchy, stepW:w1:ullimit
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:ulcauchy | blueprint-W/parts/w1-sequences.tex#bpW:w1:uniform-limit@L789-L789 | proof step of this result
EDGE: stepW:w1:ullimit | blueprint-W/parts/w1-sequences.tex#bpW:w1:uniform-limit@L794-L794 | proof step of this result
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:ulcauchy
KIND: step
TITLE: Cauchy in derivatives
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:ulcauchy@L789-L793
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:ulcauchy@L789-L793
CONTRACT_ID: stepW:w1:ulcauchy
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
EDGE: bpW:w1:cauchy | blueprint-W/parts/w1-sequences.tex#stepW:w1:ulcauchy@L791-L791 | cited at this line (step; \ref{bpW:w1:cauchy})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:ullimit
KIND: step
TITLE: Limit
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:ullimit@L794-L797
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:ullimit@L794-L797
CONTRACT_ID: stepW:w1:ullimit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-unifderiv, bpW:w1:cauchy
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-unifderiv | blueprint-W/parts/w1-sequences.tex#stepW:w1:ullimit@L795-L795 | cited at this line (step; \ref{bpW:w1:ext-unifderiv})
EDGE: bpW:w1:cauchy | blueprint-W/parts/w1-sequences.tex#stepW:w1:ullimit@L796-L796 | cited at this line (step; \ref{bpW:w1:cauchy})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:holo-analytic-fd
KIND: lemma
TITLE: Holomorphic maps of finitely many variables are analytic
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:holo-analytic-fd@L801-L811
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:holo-analytic-fd@L813-L836
CONTRACT_ID: bpW:w1:holo-analytic-fd
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:hamargin, stepW:w1:hacoef, stepW:w1:hagroup, stepW:w1:hareal
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:hamargin | blueprint-W/parts/w1-sequences.tex#bpW:w1:holo-analytic-fd@L814-L814 | proof step of this result
EDGE: stepW:w1:hacoef | blueprint-W/parts/w1-sequences.tex#bpW:w1:holo-analytic-fd@L817-L817 | proof step of this result
EDGE: stepW:w1:hagroup | blueprint-W/parts/w1-sequences.tex#bpW:w1:holo-analytic-fd@L824-L824 | proof step of this result
EDGE: stepW:w1:hareal | blueprint-W/parts/w1-sequences.tex#bpW:w1:holo-analytic-fd@L834-L834 | proof step of this result
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:hamargin
KIND: step
TITLE: Margin
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hamargin@L814-L816
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hamargin@L814-L816
CONTRACT_ID: stepW:w1:hamargin
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

NODE: stepW:w1:hacoef
KIND: step
TITLE: Coefficients
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hacoef@L817-L823
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hacoef@L817-L823
CONTRACT_ID: stepW:w1:hacoef
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-onevar, bpW:w1:ext-integral
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-onevar | blueprint-W/parts/w1-sequences.tex#stepW:w1:hacoef@L821-L821 | cited at this line (step; \ref{bpW:w1:ext-onevar})
EDGE: bpW:w1:ext-integral | blueprint-W/parts/w1-sequences.tex#stepW:w1:hacoef@L823-L823 | cited at this line (step; \ref{bpW:w1:ext-integral})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:hagroup
KIND: step
TITLE: Degree grouping
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hagroup@L824-L833
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hagroup@L824-L833
CONTRACT_ID: stepW:w1:hagroup
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

NODE: stepW:w1:hareal
KIND: step
TITLE: Real points
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hareal@L834-L835
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hareal@L834-L835
CONTRACT_ID: stepW:w1:hareal
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:complexification-lemma
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:complexification-lemma | blueprint-W/parts/w1-sequences.tex#stepW:w1:hareal@L835-L835 | cited at this line (step; \ref{bpW:w1:complexification-lemma})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:torus-analytic
KIND: corollary
TITLE: Real-analytic tori from complex strips
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:torus-analytic@L839-L844
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:torus-analytic@L846-L849
CONTRACT_ID: bpW:w1:torus-analytic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:holo-analytic-fd, bpW:w1:complexification-lemma
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:holo-analytic-fd | blueprint-W/parts/w1-sequences.tex#bpW:w1:torus-analytic@L847-L847 | cited at this line (proof; \ref{bpW:w1:holo-analytic-fd})
EDGE: bpW:w1:complexification-lemma | blueprint-W/parts/w1-sequences.tex#bpW:w1:torus-analytic@L847-L847 | cited at this line (proof; \ref{bpW:w1:complexification-lemma})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:flow
KIND: lemma
TITLE: Holomorphic flows
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:flow@L852-L866
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:flow@L868-L902
CONTRACT_ID: bpW:w1:flow
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:flowlip, stepW:w1:picard, stepW:w1:picardholo, stepW:w1:flowlim, stepW:w1:flowreal, stepW:w1:flowpar
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:flowlip | blueprint-W/parts/w1-sequences.tex#bpW:w1:flow@L869-L869 | proof step of this result
EDGE: stepW:w1:picard | blueprint-W/parts/w1-sequences.tex#bpW:w1:flow@L872-L872 | proof step of this result
EDGE: stepW:w1:picardholo | blueprint-W/parts/w1-sequences.tex#bpW:w1:flow@L876-L876 | proof step of this result
EDGE: stepW:w1:flowlim | blueprint-W/parts/w1-sequences.tex#bpW:w1:flow@L889-L889 | proof step of this result
EDGE: stepW:w1:flowreal | blueprint-W/parts/w1-sequences.tex#bpW:w1:flow@L895-L895 | proof step of this result
EDGE: stepW:w1:flowpar | blueprint-W/parts/w1-sequences.tex#bpW:w1:flow@L897-L897 | proof step of this result
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:flowlip
KIND: step
TITLE: Lipschitz region
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlip@L869-L871
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlip@L869-L871
CONTRACT_ID: stepW:w1:flowlip
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
EDGE: bpW:w1:cauchy | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlip@L871-L871 | cited at this line (step; \ref{bpW:w1:cauchy})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:picard
KIND: step
TITLE: Picard iterates
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:picard@L872-L875
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:picard@L872-L875
CONTRACT_ID: stepW:w1:picard
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

NODE: stepW:w1:picardholo
KIND: step
TITLE: Holomorphy of the iterates
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:picardholo@L876-L888
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:picardholo@L876-L888
CONTRACT_ID: stepW:w1:picardholo
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:deriv-continuous, bpW:w1:ext-integral, stepW:w1:flowlip
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:deriv-continuous | blueprint-W/parts/w1-sequences.tex#stepW:w1:picardholo@L881-L881 | cited at this line (step; \ref{bpW:w1:deriv-continuous})
EDGE: bpW:w1:ext-integral | blueprint-W/parts/w1-sequences.tex#stepW:w1:picardholo@L883-L883 | cited at this line (step; \ref{bpW:w1:ext-integral})
EDGE: stepW:w1:flowlip | blueprint-W/parts/w1-sequences.tex#stepW:w1:picardholo@L884-L884 | cited at this line (step; \ref{stepW:w1:flowlip})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:flowlim
KIND: step
TITLE: Limit
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlim@L889-L894
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlim@L889-L894
CONTRACT_ID: stepW:w1:flowlim
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-ode, bpW:w1:uniform-limit
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-ode | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlim@L891-L891 | cited at this line (step; \ref{bpW:w1:ext-ode})
EDGE: bpW:w1:uniform-limit | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlim@L893-L893 | cited at this line (step; \ref{bpW:w1:uniform-limit})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:flowreal
KIND: step
TITLE: Reality
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:flowreal@L895-L896
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:flowreal@L895-L896
CONTRACT_ID: stepW:w1:flowreal
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

NODE: stepW:w1:flowpar
KIND: step
TITLE: Parameters
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:flowpar@L897-L901
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:flowpar@L897-L901
CONTRACT_ID: stepW:w1:flowpar
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-ode
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-ode | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowpar@L900-L900 | cited at this line (step; \ref{bpW:w1:ext-ode})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:kam-space
KIND: definition
TITLE: KAM phase space, domains, norms
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:kam-space@L916-L928
PROOF_SOURCE: -
CONTRACT_ID: bpW:w1:kam-space
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

NODE: bpW:w1:kam-conventions
KIND: claim
TITLE: Conventions to carry into W4--W6
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:kam-conventions@L931-L937
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:kam-conventions@L931-L937
CONTRACT_ID: bpW:w1:kam-conventions
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:z
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:z | blueprint-W/parts/w1-sequences.tex#bpW:w1:kam-conventions@L933-L933 | cited at this line (statement; \ref{bpW:w0:z})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: remark: its justification is inline (confirm, or exclude if not a mathematical claim)

NODE: bpW:w1:kam-domain
KIND: lemma
TITLE: Domains
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:kam-domain@L939-L943
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:kam-domain@L945-L951
CONTRACT_ID: bpW:w1:kam-domain
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
EDGE: bpW:w1:embed | blueprint-W/parts/w1-sequences.tex#bpW:w1:kam-domain@L950-L950 | cited at this line (proof; \ref{bpW:w1:embed})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:fourier-l2
KIND: lemma
TITLE: Hilbert-valued Fourier series on strips
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-l2@L955-L966
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-l2@L968-L990
CONTRACT_ID: bpW:w1:fourier-l2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:shift, stepW:w1:parseval, stepW:w1:orthants, stepW:w1:fsum
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:shift | blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-l2@L969-L969 | proof step of this result
EDGE: stepW:w1:parseval | blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-l2@L975-L975 | proof step of this result
EDGE: stepW:w1:orthants | blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-l2@L980-L980 | proof step of this result
EDGE: stepW:w1:fsum | blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-l2@L984-L984 | proof step of this result
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:shift
KIND: step
TITLE: Shifted coefficients
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:shift@L969-L974
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:shift@L969-L974
CONTRACT_ID: stepW:w1:shift
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

NODE: stepW:w1:parseval
KIND: step
TITLE: Parseval
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:parseval@L975-L979
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:parseval@L975-L979
CONTRACT_ID: stepW:w1:parseval
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-fourier
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-fourier | blueprint-W/parts/w1-sequences.tex#stepW:w1:parseval@L978-L978 | cited at this line (step; \ref{bpW:w1:ext-fourier})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:orthants
KIND: step
TITLE: Orthants
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:orthants@L980-L983
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:orthants@L980-L983
CONTRACT_ID: stepW:w1:orthants
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

NODE: stepW:w1:fsum
KIND: step
TITLE: Summation
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fsum@L984-L989
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fsum@L984-L989
CONTRACT_ID: stepW:w1:fsum
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
EDGE: bpW:w1:uniform-limit | blueprint-W/parts/w1-sequences.tex#stepW:w1:fsum@L986-L986 | cited at this line (step; \ref{bpW:w1:uniform-limit})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:fourier-banach
KIND: lemma
TITLE: Banach-valued Fourier coefficients on strips
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-banach@L996-L1012
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-banach@L1014-L1029
CONTRACT_ID: bpW:w1:fourier-banach
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:fbdual, stepW:w1:fbdecay, stepW:w1:fbsum, stepW:w1:fbconv, bpW:w1:lattice
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:fbdual | blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-banach@L1015-L1015 | proof step of this result
EDGE: stepW:w1:fbdecay | blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-banach@L1019-L1019 | proof step of this result
EDGE: stepW:w1:fbsum | blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-banach@L1023-L1023 | proof step of this result
EDGE: stepW:w1:fbconv | blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-banach@L1025-L1025 | proof step of this result
EDGE: bpW:w1:lattice | blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-banach@L1005-L1005 | cited at this line (statement; \ref{bpW:w1:lattice})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:fbdual
KIND: step
TITLE: Scalar reduction
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fbdual@L1015-L1018
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fbdual@L1015-L1018
CONTRACT_ID: stepW:w1:fbdual
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-onevar
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-onevar | blueprint-W/parts/w1-sequences.tex#stepW:w1:fbdual@L1018-L1018 | cited at this line (step; \ref{bpW:w1:ext-onevar})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:fbdecay
KIND: step
TITLE: Scalar decay
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fbdecay@L1019-L1022
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fbdecay@L1019-L1022
CONTRACT_ID: stepW:w1:fbdecay
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

NODE: stepW:w1:fbsum
KIND: step
TITLE: Lattice sum
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fbsum@L1023-L1024
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fbsum@L1023-L1024
CONTRACT_ID: stepW:w1:fbsum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:lattice
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:lattice | blueprint-W/parts/w1-sequences.tex#stepW:w1:fbsum@L1024-L1024 | cited at this line (step; \ref{bpW:w1:lattice})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:fbconv
KIND: step
TITLE: Summation
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fbconv@L1025-L1028
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fbconv@L1025-L1028
CONTRACT_ID: stepW:w1:fbconv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:uniform-limit, bpW:w1:ext-integral
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:uniform-limit | blueprint-W/parts/w1-sequences.tex#stepW:w1:fbconv@L1027-L1027 | cited at this line (step; \ref{bpW:w1:uniform-limit})
EDGE: bpW:w1:ext-integral | blueprint-W/parts/w1-sequences.tex#stepW:w1:fbconv@L1028-L1028 | cited at this line (step; \ref{bpW:w1:ext-integral})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:lattice
KIND: lemma
TITLE: Weighted lattice sums
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:lattice@L1033-L1047
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:lattice@L1049-L1065
CONTRACT_ID: bpW:w1:lattice
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:latprod, stepW:w1:latcount, stepW:w1:latweight, stepW:w1:latdiv
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:latprod | blueprint-W/parts/w1-sequences.tex#bpW:w1:lattice@L1050-L1050 | proof step of this result
EDGE: stepW:w1:latcount | blueprint-W/parts/w1-sequences.tex#bpW:w1:lattice@L1054-L1054 | proof step of this result
EDGE: stepW:w1:latweight | blueprint-W/parts/w1-sequences.tex#bpW:w1:lattice@L1057-L1057 | proof step of this result
EDGE: stepW:w1:latdiv | blueprint-W/parts/w1-sequences.tex#bpW:w1:lattice@L1062-L1062 | proof step of this result
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:latprod
KIND: step
TITLE: Product
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:latprod@L1050-L1053
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:latprod@L1050-L1053
CONTRACT_ID: stepW:w1:latprod
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-series
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-series | blueprint-W/parts/w1-sequences.tex#stepW:w1:latprod@L1052-L1052 | cited at this line (step; \ref{bpW:w1:ext-series})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:latcount
KIND: step
TITLE: Counting
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:latcount@L1054-L1056
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:latcount@L1054-L1056
CONTRACT_ID: stepW:w1:latcount
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

NODE: stepW:w1:latweight
KIND: step
TITLE: Weighted sum
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:latweight@L1057-L1061
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:latweight@L1057-L1061
CONTRACT_ID: stepW:w1:latweight
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

NODE: stepW:w1:latdiv
KIND: step
TITLE: Divisor weights
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:latdiv@L1062-L1064
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:latdiv@L1062-L1064
CONTRACT_ID: stepW:w1:latdiv
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

NODE: bpW:w1:operator-fourier
KIND: claim
TITLE: The operator-valued Fourier step of P96-K Lemma~1
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:operator-fourier@L1068-L1104
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:operator-fourier@L1068-L1104
CONTRACT_ID: bpW:w1:operator-fourier
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:fourier-l2, bpW:w1:transport, bpW:w1:fourier-banach, bpW:w1:schur, bpW:w1:lattice
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:fourier-l2 | blueprint-W/parts/w1-sequences.tex#bpW:w1:operator-fourier@L1074-L1074 | cited at this line (statement; \ref{bpW:w1:fourier-l2})
EDGE: bpW:w1:transport | blueprint-W/parts/w1-sequences.tex#bpW:w1:operator-fourier@L1084-L1084 | cited at this line (statement; \ref{bpW:w1:transport})
EDGE: bpW:w1:fourier-banach | blueprint-W/parts/w1-sequences.tex#bpW:w1:operator-fourier@L1093-L1093 | cited at this line (statement; \ref{bpW:w1:fourier-banach})
EDGE: bpW:w1:schur | blueprint-W/parts/w1-sequences.tex#bpW:w1:operator-fourier@L1094-L1094 | cited at this line (statement; \ref{bpW:w1:schur})
EDGE: bpW:w1:lattice | blueprint-W/parts/w1-sequences.tex#bpW:w1:operator-fourier@L1096-L1096 | cited at this line (statement; \ref{bpW:w1:lattice})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: remark: its justification is inline (confirm, or exclude if not a mathematical claim)

NODE: bpW:w1:schur
KIND: lemma
TITLE: Hilbert-matrix bound
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:schur@L1110-L1121
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:schur@L1123-L1138
CONTRACT_ID: bpW:w1:schur
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:rows, stepW:w1:schurtest, stepW:w1:diagcomb, stepW:w1:schurweights, bpW:w1:transport
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:rows | blueprint-W/parts/w1-sequences.tex#bpW:w1:schur@L1124-L1124 | proof step of this result
EDGE: stepW:w1:schurtest | blueprint-W/parts/w1-sequences.tex#bpW:w1:schur@L1128-L1128 | proof step of this result
EDGE: stepW:w1:diagcomb | blueprint-W/parts/w1-sequences.tex#bpW:w1:schur@L1131-L1131 | proof step of this result
EDGE: stepW:w1:schurweights | blueprint-W/parts/w1-sequences.tex#bpW:w1:schur@L1136-L1136 | proof step of this result
EDGE: bpW:w1:transport | blueprint-W/parts/w1-sequences.tex#bpW:w1:schur@L1119-L1119 | cited at this line (statement; \ref{bpW:w1:transport})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:rows
KIND: step
TITLE: Row and column sums
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:rows@L1124-L1127
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:rows@L1124-L1127
CONTRACT_ID: stepW:w1:rows
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-series
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-series | blueprint-W/parts/w1-sequences.tex#stepW:w1:rows@L1126-L1126 | cited at this line (step; \ref{bpW:w1:ext-series})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:schurtest
KIND: step
TITLE: Schur test
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:schurtest@L1128-L1130
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:schurtest@L1128-L1130
CONTRACT_ID: stepW:w1:schurtest
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-lp
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-lp | blueprint-W/parts/w1-sequences.tex#stepW:w1:schurtest@L1130-L1130 | cited at this line (step; \ref{bpW:w1:ext-lp})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:diagcomb
KIND: step
TITLE: Diagonal and combination
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:diagcomb@L1131-L1135
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:diagcomb@L1131-L1135
CONTRACT_ID: stepW:w1:diagcomb
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: TODO
SOURCE_QUANTIFIERS: TODO
SOURCE_CONCLUSION: TODO
CONSTANT_SCOPE: TODO
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:multiplier
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:multiplier | blueprint-W/parts/w1-sequences.tex#stepW:w1:diagcomb@L1132-L1132 | cited at this line (step; \ref{bpW:w1:multiplier})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: mechanical-preextract
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:schurweights
KIND: step
TITLE: Weights
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:schurweights@L1136-L1137
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:schurweights@L1136-L1137
CONTRACT_ID: stepW:w1:schurweights
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

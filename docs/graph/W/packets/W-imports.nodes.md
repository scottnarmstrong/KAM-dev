NODE: K:bp:p1:decay
KIND: external
TITLE: [K] Coefficient decay
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:decay@L786-L789
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p1:decay
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing conventions K p1 L24-L47: n >= 1, rho > 0, u takes values in a finite-dimensional complex normed W; u holomorphic, bounded and 1-periodic on T_rho
SOURCE_QUANTIFIERS: rho, u; k in Z^n; rho' with 0<=rho'<rho
SOURCE_CONCLUSION: |hat u_k| <= e^{-2 pi |k|_1 rho'} ||u||_rho
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-imports
REVIEWER: sol-delta-W-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p1:decay; shared Lean provider. There: KIND lemma, contract bp:p1:decay v1. Source-context correction proposed by sol-review-W-imports: these inherited typing data are explicit in blueprint/parts/p1-analysis.tex L24-L47. The input four fields were exact copies of K; the upstream K record needs the same review before a regenerated import can again be an exact copy.

NODE: K:bp:p1:fourier-basic
KIND: external
TITLE: [K] Fourier coefficients of periodic functions
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:fourier-basic@L757-L768
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p1:fourier-basic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing convention K p1 L34-L47: n >= 1, Fourier indices in Z^n, period one; v C-valued (componentwise for vector/matrix); (a) v continuous, 1-periodic, C^1; (b) v continuous, 1-periodic, sum |hat v_k| finite; (c) r>0, v holomorphic and 1-periodic on T_r, not necessarily bounded, all hat v_k=0
SOURCE_QUANTIFIERS: v; k in Z^n; ell; omega in C^n; r
SOURCE_CONCLUSION: (a) hat(d_ell v)_k = 2 pi i k_ell hat v_k and hat(d_omega v)_k = 2 pi i (k.omega) hat v_k; (b) v(x)=sum hat v_k chi_k(x) for all x, so v=0 if all hat v_k=0; (c) v=0 on T_r
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-imports
REVIEWER: sol-delta-W-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p1:fourier-basic; shared Lean provider. There: KIND lemma, contract bp:p1:fourier-basic v1. Source-context correction proposed by sol-review-W-imports: these inherited typing data are explicit in blueprint/parts/p1-analysis.tex L24-L47. The input four fields were exact copies of K; the upstream K record needs the same review before a regenerated import can again be an exact copy.

NODE: K:bp:p1:strip-identity
KIND: external
TITLE: [K] Identity theorem on strips
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:strip-identity@L531-L534
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p1:strip-identity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing conventions K p1 L24-L47: n >= 1 and W a finite-dimensional complex normed space; r>0; v holomorphic on T_r with values in W; v(x)=0 for all real x
SOURCE_QUANTIFIERS: r>0 ; v
SOURCE_CONCLUSION: v=0 on T_r
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-imports
REVIEWER: sol-delta-W-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p1:strip-identity; shared Lean provider. There: KIND lemma, contract bp:p1:strip-identity v1. Source-context correction proposed by sol-review-W-imports: these inherited typing data are explicit in blueprint/parts/p1-analysis.tex L24-L47. The input four fields were exact copies of K; the upstream K record needs the same review before a regenerated import can again be an exact copy.

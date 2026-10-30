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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-imports
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-imports
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p1:fourier-basic; shared Lean provider. There: KIND lemma, contract bp:p1:fourier-basic v1. Source-context correction proposed by sol-review-W-imports: these inherited typing data are explicit in blueprint/parts/p1-analysis.tex L24-L47. The input four fields were exact copies of K; the upstream K record needs the same review before a regenerated import can again be an exact copy.

NODE: K:bp:p1:holomorphic-analytic
KIND: external
TITLE: [K] Holomorphic maps are analytic
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:holomorphic-analytic@L296-L312
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p1:holomorphic-analytic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing convention K p1 L24-L32: W is a finite-dimensional complex normed space; m is a natural-number dimension; U in C^m open; F:U->W holomorphic; (a) z_0 in U, r>0 with P-bar(z_0,r) in U, A=max_{P-bar(z_0,r)}|F|; (b) U_R=U cap R^m, x_0 in U_R; W=C^p and F(U_R) in R^p for the real clause
SOURCE_QUANTIFIERS: F,U,W,m; then z_0,r (A determined); alpha in N^m
SOURCE_CONCLUSION: (a) exist c_alpha in W with |c_alpha|<=A r^-|alpha| and F(z)=sum_alpha c_alpha (z-z_0)^alpha on P(z_0,r), absolutely convergent; F analytic on U; (b) F|U_R real-analytic near each x_0 (power series in x-x_0, absolutely convergent); real coefficients if W=C^p and F(U_R) in R^p
CONSTANT_SCOPE: c_alpha depends on F,z_0,r only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-imports
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p1:holomorphic-analytic; shared Lean provider. There: KIND lemma, contract bp:p1:holomorphic-analytic v1. Source-context correction proposed by sol-review-W-imports: these inherited typing data are explicit in blueprint/parts/p1-analysis.tex L24-L47. The input four fields were exact copies of K; the upstream K record needs the same review before a regenerated import can again be an exact copy.

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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-imports
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p1:strip-identity; shared Lean provider. There: KIND lemma, contract bp:p1:strip-identity v1. Source-context correction proposed by sol-review-W-imports: these inherited typing data are explicit in blueprint/parts/p1-analysis.tex L24-L47. The input four fields were exact copies of K; the upstream K record needs the same review before a regenerated import can again be an exact copy.

NODE: K:step:p1:dec-shift
KIND: external
TITLE: [K] Shifting one variable
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:dec-shift@L800-L811
PROOF_SOURCE: -
CONTRACT_ID: K:step:p1:dec-shift
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K p1 proof context L792-L798: n >= 1, rho > 0; W a finite-dimensional complex normed space; u:T_rho -> W holomorphic, bounded and 1-periodic; k in Z^n; 0 <= rho_prime < rho; t_l=-rho_prime sgn(k_l) with sgn(0)=0; t^(j)=(t_1,...,t_j,0,...,0); I_j=int_[0,1]^n u(x+i t^(j)) exp(-2 pi i k.(x+i t^(j))) dx
SOURCE_QUANTIFIERS: for every n,rho,W,u,k,rho_prime as stated; for each 1 <= j <= n and x_l in [0,1] for l != j
SOURCE_CONCLUSION: I_{j-1}=I_j for 1<=j<=n
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-imports
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node step:p1:dec-shift; shared Lean provider. There: KIND step, contract step:p1:dec-shift v1. Source-context correction proposed by sol-review-W-imports: these inherited typing data are explicit in blueprint/parts/p1-analysis.tex L24-L47 and L792-L811. The input four fields were exact copies of K; the upstream K record needs the same review before a regenerated import can again be an exact copy.

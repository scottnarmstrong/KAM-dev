<!-- Staged append-only AMEND records for docs/graph/K/AMENDMENTS.md (track-W global review G2, ruling root-b8 (a)).
     Not loaded by the linter. After an independent PASS (tag sol-kamend-W), set each REVIEWER to that tag, append the
     records verbatim to AMENDMENTS.md and reassemble K (the assembler copies AMENDMENTS.md into DEPGRAPH.md). -->

AMEND: K-A045-w-findim-decay
TARGET: bp:p1:decay
AUTHOR: claude-suborch-W
REVIEWER: <pending sol-kamend-W>
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: typing conventions K p1 L24-L47: n >= 1, rho > 0, u takes values in a finite-dimensional complex normed W; u holomorphic, bounded and 1-periodic on T_rho
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 typing conventions made explicit in the source premises: p1-analysis.tex L26 (W denotes a finite-dimensional complex normed space) and L37-L39 (positive widths, n >= 1); the statement L786-L789 is for such u. Found by the track-W global review (docs/graph/W/reviews/GLOBAL-review.md G2); ruling root-b8 option (a). New field = the convention prefix plus the old premises; no mathematical change, hence no contract-version bump (as K-A001-K-A044). The text equals the reviewed W import record.

AMEND: K-A046-w-conventions-fourier-basic
TARGET: bp:p1:fourier-basic
AUTHOR: claude-suborch-W
REVIEWER: <pending sol-kamend-W>
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: typing convention K p1 L34-L47: n >= 1, Fourier indices in Z^n, period one; v C-valued (componentwise for vector/matrix); (a) v continuous, 1-periodic, C^1; (b) v continuous, 1-periodic, sum |hat v_k| finite; (c) r>0, v holomorphic and 1-periodic on T_r, not necessarily bounded, all hat v_k=0
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 typing conventions made explicit in the source premises: p1-analysis.tex L36-L47 (1-periodicity on T_r, chi_k for k in Z^n, hat v_k entrywise) and L37-L39 (n >= 1); the statement L757-L768 is read in these conventions. Found by the track-W global review (docs/graph/W/reviews/GLOBAL-review.md G2); ruling root-b8 option (a). New field = the convention prefix plus the old premises; no mathematical change, hence no contract-version bump (as K-A001-K-A044). The text equals the reviewed W import record.

AMEND: K-A047-w-findim-holomorphic-analytic
TARGET: bp:p1:holomorphic-analytic
AUTHOR: claude-suborch-W
REVIEWER: <pending sol-kamend-W>
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: typing convention K p1 L24-L32: W is a finite-dimensional complex normed space; m is a natural-number dimension; U in C^m open; F:U->W holomorphic; (a) z_0 in U, r>0 with P-bar(z_0,r) in U, A=max_{P-bar(z_0,r)}|F|; (b) U_R=U cap R^m, x_0 in U_R; W=C^p and F(U_R) in R^p for the real clause
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 typing conventions made explicit in the source premises: p1-analysis.tex L26 (W finite-dimensional complex normed) and L29-L32 (holomorphic on open U in C^m, operator norms); the statement L296-L312 has F : U -> W. Found by the track-W global review (docs/graph/W/reviews/GLOBAL-review.md G2); ruling root-b8 option (a). New field = the convention prefix plus the old premises; no mathematical change, hence no contract-version bump (as K-A001-K-A044). The text equals the reviewed W import record.

AMEND: K-A048-w-findim-strip-identity
TARGET: bp:p1:strip-identity
AUTHOR: claude-suborch-W
REVIEWER: <pending sol-kamend-W>
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: typing conventions K p1 L24-L47: n >= 1 and W a finite-dimensional complex normed space; r>0; v holomorphic on T_r with values in W; v(x)=0 for all real x
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 typing conventions made explicit in the source premises: p1-analysis.tex L26 (W finite-dimensional complex normed) and L37-L39 (n >= 1); the statement L531-L534 has values in W. Found by the track-W global review (docs/graph/W/reviews/GLOBAL-review.md G2); ruling root-b8 option (a). New field = the convention prefix plus the old premises; no mathematical change, hence no contract-version bump (as K-A001-K-A044). The text equals the reviewed W import record.

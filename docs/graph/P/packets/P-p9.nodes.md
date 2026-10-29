NODE: bpP:p9:e-spec
KIND: external
TITLE: Real spectral theorem
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:e-spec@L20-L20
PROOF_SOURCE: -
CONTRACT_ID: bpP:p9:e-spec
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: M real symmetric n x n matrix
SOURCE_QUANTIFIERS: n, M
SOURCE_CONCLUSION: M=varrho diag(lambda) varrho^T with varrho in O(n) (orthonormal eigenbasis) and det(sI-M)=prod_j (s-lambda_j); (Mathlib spectral theorem, charpoly); eigenvalue enumeration of Mathlib is arbitrary and not analytic in parameters
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9
REVIEWER: sol-review-P-k
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external item that cites \ref{bpP:p9:local-analytic}: if it only restates the cited external, exclude it as an alias and point its consumers at the cited node (SPEC)

NODE: bpP:p9:e-ift
KIND: external
TITLE: Analytic implicit function theorem
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:e-ift@L21-L21
PROOF_SOURCE: -
CONTRACT_ID: bpP:p9:e-ift
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: p(w,s) real analytic near (w0,s0) in R^m x R; p(w0,s0)=0; d_s p(w0,s0)!=0
SOURCE_QUANTIFIERS: m, p, (w0,s0)
SOURCE_CONCLUSION: exists real analytic s(w) near w0 with s(w0)=s0 and p(w,s(w))=0, and it is the only continuous solution near (w0,s0) (analytic implicit function theorem, scalar condition)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9
REVIEWER: sol-review-P-k
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external; adds the analytic (omega-level) and uniqueness content to the C^1 inverse function theorem bpP:p1:ext-ift, so not an alias

NODE: bpP:p9:e-fts
KIND: external
TITLE: Fundamental theorem of symmetric polynomials
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:e-fts@L22-L22
PROOF_SOURCE: -
CONTRACT_ID: bpP:p9:e-fts
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: symmetric polynomial in sigma_1..sigma_n with real coefficients
SOURCE_QUANTIFIERS: n, polynomial
SOURCE_CONCLUSION: it is a polynomial in the elementary symmetric polynomials, which are up to sign the coefficients of det(sI-M)=prod(s-sigma_j)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9+sol-review-P-k
REVIEWER: sol-delta-P-k
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p9:e-id
KIND: external
TITLE: Identity theorem
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:e-id@L23-L23
PROOF_SOURCE: -
CONTRACT_ID: bpP:p9:e-id
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: real analytic function on a connected open set A in R^m, vanishing on a nonempty open subset (clause 1); not identically zero (clause 2)
SOURCE_QUANTIFIERS: m, A, function
SOURCE_CONCLUSION: it vanishes identically; if not identically zero its zero set is closed, has empty interior and Lebesgue measure zero
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9
REVIEWER: sol-review-P-k
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p9:e-ibp
KIND: external
TITLE: bpP:p9:e-ibp
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:e-ibp@L24-L24
PROOF_SOURCE: -
CONTRACT_ID: bpP:p9:e-ibp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: integration by parts on an interval; continuous nonnegative function positive somewhere
SOURCE_QUANTIFIERS: interval, function
SOURCE_CONCLUSION: integration by parts formula; the integral of a continuous nonnegative function positive somewhere is positive
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9
REVIEWER: sol-review-P-k
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p9:conv#data
KIND: definition
TITLE: Conventions of Part 9 (norms, Sym_n, increasing labelling, comparison with max norms)
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:conv#data@L15-L16
PROOF_SOURCE: -
CONTRACT_ID: bpP:p9:conv#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n>=1; G,m0,m,kappa and increasing axes a_1<...<a_n as in Part 8; Lambda_i=m_i sqrt(kappa a_i); frakt a_ij, frakt b_ij, hat q, Q_h=Delta^-1 hat q Delta^-1 of Definition coeffs; ambient spaces Fin n -> R and Fin n -> C with max norm
SOURCE_QUANTIFIERS: n,G,m0,m,a; then x in R^n or C^n, M in Sym_n
SOURCE_CONCLUSION: defines the Euclidean norm of x, the induced operator norm of M and the Frobenius norm (operator norm <= Frobenius norm; entries and columns bounded by the operator norm), e_j, Sym_n; states the comparison with the max norms ¦x¦_inf<=¦x¦<=sqrt n ¦x¦_inf and operator norm comparison with factor sqrt n; Q_h=Q_h(a) real analytic in a on {a_1<...<a_n}; eigenvalues sigma_1<...<sigma_n labelled increasingly where simple, independent of the planet order
CONSTANT_SCOPE: constants of Part 9 are stated in Euclidean norms; no constant is chosen here
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p8:coeffs, bpP:p8:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p8:coeffs | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:conv#data@L15-L15 | frakt a, frakt b, hat q, Q_h, Delta of Definition coeffs and real analyticity of Q_h(a)
EDGE: bpP:p8:conv#data | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:conv#data@L15-L15 | data of Part 8 (n, G, m0, m, kappa, axes)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9
REVIEWER: sol-review-P-k
LEAN_STATUS: PROVED
LEAN_REF: length2, op2, frobenius, sorted, isSO, opMax, norm_compare, norm_compare_operator (KAM/Planetary/SecularSpectrum/Norms.lean); coeffs_analytic, SecularSpectrum.sigma (KAM/Planetary/SecularForm/Coefficients.lean)
LEAN_NOTE: composite of audits S9-N PASS WITH NOTES + S8-C PASS WITH NOTES
NOTE: created from p9:prose-L15-L16 (SPEC section data); includes the inline label bpP:p9:norm-compare; consumers: definite, local-analytic, diagonalize (step d-c), good, n2

NODE: bpP:p9:l75
KIND: lemma
TITLE: Hadamard; Fej04r Lemma 75
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:l75@L70-L75
PROOF_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:l75@L76-L78
CONTRACT_ID: bpP:p9:l75
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Q in Sym_n with q_jk>=0 for j!=k; delta q_j:=-q_jj-sum_{l!=j} q_jl
SOURCE_QUANTIFIERS: n, Q, x in R^n
SOURCE_CONCLUSION: x^T Q x=-sum_j delta q_j x_j^2-sum_{j<k} q_jk (x_j-x_k)^2; if all delta q_j>=0 then Q<=0; if c=min delta q_j>0 then x^T Q x<=-c ¦x¦^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p9:l75, bpP:p9:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p9:l75 | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:l75@L77-L77 | proof step Expansion
EDGE: bpP:p9:conv#data | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:l75@L71-L71 | Sym_n and Euclidean norm
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9
REVIEWER: sol-review-P-k
LEAN_STATUS: PROVED
LEAN_REF: l75, l75_bound (KAM/Planetary/SecularSpectrum/Definiteness/Hadamard.lean)
LEAN_NOTE: audit S9-D PASS WITH NOTES (audit-2, F1 hygiene finding closed; audit-1 FAIL superseded)
NOTE: -

NODE: stepP:p9:l75
KIND: step
TITLE: Expansion
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:l75@L77-L77
PROOF_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:l75@L77-L77
CONTRACT_ID: stepP:p9:l75
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the source premises of bpP:p9:l75: Q in Sym_n, q_jk>=0 for j!=k, delta q_j:=-q_jj-sum_{l!=j}q_jl; x in R^n
SOURCE_QUANTIFIERS: x in R^n
SOURCE_CONCLUSION: sum of the two displayed terms equals sum q_jj x_j^2+2 sum_{j<k} q_jk x_j x_k=x^T Q x
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p9:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p9:conv#data | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:l75@L77-L77 | The Euclidean norm, orthonormal/orthogonal matrix convention or Sym_n typing used in this source unit is fixed here.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9+sol-review-P-k
REVIEWER: sol-delta-P-k
LEAN_STATUS: PROVED
LEAN_REF: l75 (KAM/Planetary/SecularSpectrum/Definiteness/Hadamard.lean)
LEAN_NOTE: audit S9-D PASS WITH NOTES (audit-2, F1 hygiene finding closed; audit-1 FAIL superseded)
NOTE: -

NODE: bpP:p9:l74
KIND: lemma
TITLE: Laplace coefficients: $b_s^{(1)}>b_s^{(2)}$; the case of Fej04r Lemma 74 that is needed
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:l74@L80-L85
PROOF_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:l74@L86-L89
CONTRACT_ID: bpP:p9:l74
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: s>0, alpha in (0,1), A(t)=1+alpha^2-2 alpha cos t, b_s^(k) of Definition laplace-def
SOURCE_QUANTIFIERS: s, alpha
SOURCE_CONCLUSION: b_s^(1)(alpha)-b_s^(2)(alpha)=(2 s alpha/pi) int_0^pi sin^2 t (1-cos t) A(t)^(-s-1) dt>0; in particular b_{3/2}^(1)>b_{3/2}^(2)>0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p9:l74-red, stepP:p9:l74-ibp, bpP:p8:laplace-def, bpP:p8:laplace
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p9:l74-red | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:l74@L87-L87 | proof step Reduction to [0,pi]
EDGE: stepP:p9:l74-ibp | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:l74@L88-L88 | proof step Integration by parts
EDGE: bpP:p8:laplace-def | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:l74@L81-L81 | b_s^(k) and A(t)
EDGE: bpP:p8:laplace | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:l74@L83-L83 | positivity b_{3/2}^(2)>0 from the series
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9
REVIEWER: sol-review-P-k
LEAN_STATUS: PROVED
LEAN_REF: l74 (KAM/Planetary/SecularSpectrum/Definiteness/Laplace.lean)
LEAN_NOTE: audit S9-D PASS WITH NOTES (audit-2, F1 hygiene finding closed; audit-1 FAIL superseded)
NOTE: -

NODE: stepP:p9:l74-red
KIND: step
TITLE: Reduction to $[0,\pi]$
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:l74-red@L87-L87
PROOF_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:l74-red@L87-L87
CONTRACT_ID: stepP:p9:l74-red
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the source premises of bpP:p9:l74: s>0, alpha in (0,1), A(t):=1+alpha^2-2 alpha cos t and the Laplace coefficients of bpP:p8:laplace-def; define w(t):=A(t)^(-s)
SOURCE_QUANTIFIERS: k in {1,2}
SOURCE_CONCLUSION: b_s^(k)=pi^-1 int_0^pi cos(kt) w(t) dt
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p8:laplace-def
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p8:laplace-def | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:l74-red@L87-L87 | definition of b_s^(k) as a period integral
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9+sol-review-P-k
REVIEWER: sol-delta-P-k
LEAN_STATUS: PROVED
LEAN_REF: laplace_def_eq_half (KAM/Planetary/SecularSpectrum/Definiteness/Laplace.lean)
LEAN_NOTE: audit S9-D PASS WITH NOTES (audit-2, F1 hygiene finding closed; audit-1 FAIL superseded)
NOTE: -

NODE: stepP:p9:l74-ibp
KIND: step
TITLE: Integration by parts
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:l74-ibp@L88-L88
PROOF_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:l74-ibp@L88-L88
CONTRACT_ID: stepP:p9:l74-ibp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the source premises of bpP:p9:l74: s>0, alpha in (0,1), A(t):=1+alpha^2-2 alpha cos t; define w(t):=A(t)^(-s), H(t):=sin t(1-cos t)
SOURCE_QUANTIFIERS: s>0, alpha in (0,1)
SOURCE_CONCLUSION: b_s^(1)-b_s^(2)=-pi^-1 int_0^pi H w prime dt=(2 s alpha/pi) int sin^2 t (1-cos t) A^(-s-1) dt>0; b_{3/2}^(2)>0 by positivity of the series
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p9:e-ibp, stepP:p9:l74-red, bpP:p8:laplace, bpP:p8:laplace-def
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p9:e-ibp | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:l74-ibp@L88-L88 | integration by parts and positivity of the integral
EDGE: stepP:p9:l74-red | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:l74-ibp@L88-L88 | reduction to [0,pi]
EDGE: bpP:p8:laplace | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:l74-ibp@L88-L88 | positivity of b_s^(k) from the series
EDGE: bpP:p8:laplace-def | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:l74-ibp@L88-L88 | The Laplace coefficient integral and its normalization are used in the integration-by-parts identity.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9+sol-review-P-k
REVIEWER: sol-delta-P-k
LEAN_STATUS: PROVED
LEAN_REF: ibp_formula (KAM/Planetary/SecularSpectrum/Definiteness/Laplace.lean)
LEAN_NOTE: audit S9-D PASS WITH NOTES (audit-2, F1 hygiene finding closed; audit-1 FAIL superseded)
NOTE: -

NODE: bpP:p9:definite
KIND: proposition
TITLE: Fej04r Proposition 73
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:definite@L91-L98
PROOF_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:definite@L99-L103
CONTRACT_ID: bpP:p9:definite
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n>=2; a_1<...<a_n; all masses positive; frakt a_ij, frakt b_ij of Definition coeffs; c_hat q(a):=min_j sum_{k!=j}(frakt a_jk-frakt b_jk)
SOURCE_QUANTIFIERS: n,G,m,a; then x in R^n
SOURCE_CONCLUSION: c_hat q(a)>0; x^T hat q x<=-sum_j(sum_{k!=j}(a_jk-b_jk)) x_j^2<=-c ¦x¦^2; x^T Q_h x<=-c_hat q(a)/max_i Lambda_i ¦x¦^2; hat q, Q_h negative definite, all eigenvalues sigma_j<=-c/max Lambda<0, Omega_j=2 sigma_j<0; the bound is continuous hence locally uniformly positive on {a_1<...<a_n}
CONSTANT_SCOPE: c_hat q depends on (G,m,a) only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p9:p73-dom, stepP:p9:p73-had, stepP:p9:p73-cong, bpP:p8:coeffs, bpP:p9:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p9:p73-dom | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:definite@L100-L100 | proof step Strong diagonal dominance
EDGE: stepP:p9:p73-had | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:definite@L101-L101 | proof step Hadamard
EDGE: stepP:p9:p73-cong | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:definite@L102-L102 | proof step Congruence
EDGE: bpP:p8:coeffs | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:definite@L92-L92 | frakt a, frakt b, hat q, Q_h
EDGE: bpP:p9:conv#data | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:definite@L92-L92 | Euclidean norm, Sym_n
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9
REVIEWER: sol-review-P-k
LEAN_STATUS: PROVED
LEAN_REF: coercivity, definite (KAM/Planetary/SecularSpectrum/Definiteness.lean)
LEAN_NOTE: audit S9-D PASS WITH NOTES (audit-2, F1 hygiene finding closed; audit-1 FAIL superseded)
NOTE: -

NODE: stepP:p9:p73-dom
KIND: step
TITLE: Strong diagonal dominance
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:p73-dom@L100-L100
PROOF_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:p73-dom@L100-L100
CONTRACT_ID: stepP:p9:p73-dom
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the source premises of bpP:p9:definite: n>=2, positive axes a_1<...<a_n, positive G,m0,m with kappa=G m0 and Lambda_i=m_i sqrt(kappa a_i), and the coefficients of bpP:p8:coeffs; c_hat q:=min_j sum_{k!=j}(frakt a_jk-frakt b_jk)
SOURCE_QUANTIFIERS: n>=2; j
SOURCE_CONCLUSION: delta hat q_j=sum_{k!=j}(a_jk-b_jk)>0 for every j
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p8:coeffs, bpP:p9:l74
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p8:coeffs | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:p73-dom@L100-L100 | definitions of hat q, frakt a, frakt b and symmetry
EDGE: bpP:p9:l74 | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:p73-dom@L100-L100 | b_{3/2}^(1)>b_{3/2}^(2)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9+sol-review-P-k
REVIEWER: sol-delta-P-k
LEAN_STATUS: PROVED
LEAN_REF: pairA_sub_pairB_pos, dominance_qhat, gap_pos (KAM/Planetary/SecularSpectrum/Definiteness.lean); dominance (KAM/Planetary/SecularSpectrum/Definiteness/Hadamard.lean)
LEAN_NOTE: audit S9-D PASS WITH NOTES (audit-2, F1 hygiene finding closed; audit-1 FAIL superseded)
NOTE: -

NODE: stepP:p9:p73-had
KIND: step
TITLE: Lemma~\ref{bpP:p9:l75}
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:p73-had@L101-L101
PROOF_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:p73-had@L101-L101
CONTRACT_ID: stepP:p9:p73-had
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the source premises of bpP:p9:definite: n>=2, positive axes a_1<...<a_n, positive G,m0,m with kappa=G m0 and Lambda_i=m_i sqrt(kappa a_i), and the coefficients of bpP:p8:coeffs; c_hat q:=min_j sum_{k!=j}(frakt a_jk-frakt b_jk)
SOURCE_QUANTIFIERS: x in R^n
SOURCE_CONCLUSION: x^T hat q x<=-sum_j delta hat q_j x_j^2<=-c_hat q ¦x¦^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p9:l75, stepP:p9:p73-dom, bpP:p9:conv#data, bpP:p8:coeffs
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p9:l75 | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:p73-had@L101-L101 | Hadamard identity and the two inequalities
EDGE: stepP:p9:p73-dom | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:p73-had@L101-L101 | delta hat q_j>0 and hat q_jk>0 for j!=k
EDGE: bpP:p9:conv#data | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:p73-had@L101-L101 | The Euclidean norm, orthonormal/orthogonal matrix convention or Sym_n typing used in this source unit is fixed here.
EDGE: bpP:p8:coeffs | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:p73-had@L101-L101 | The matrix hat q to which l75 is applied is the secular coefficient matrix.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9+sol-review-P-k
REVIEWER: sol-delta-P-k
LEAN_STATUS: PROVED
LEAN_REF: l75_bound (KAM/Planetary/SecularSpectrum/Definiteness/Hadamard.lean); definite (KAM/Planetary/SecularSpectrum/Definiteness.lean)
LEAN_NOTE: audit S9-D PASS WITH NOTES (audit-2, F1 hygiene finding closed; audit-1 FAIL superseded)
NOTE: -

NODE: stepP:p9:p73-cong
KIND: step
TITLE: Congruence
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:p73-cong@L102-L102
PROOF_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:p73-cong@L102-L102
CONTRACT_ID: stepP:p9:p73-cong
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the source premises of bpP:p9:definite: n>=2, positive axes a_1<...<a_n, positive G,m0,m with kappa=G m0 and Lambda_i=m_i sqrt(kappa a_i), and the coefficients of bpP:p8:coeffs; c_hat q:=min_j sum_{k!=j}(frakt a_jk-frakt b_jk)
SOURCE_QUANTIFIERS: x in R^n
SOURCE_CONCLUSION: x^T Q_h x<=-c ¦x¦^2/max Lambda; every eigenvalue satisfies sigma_j<=-c/max Lambda; the bound is continuous in a
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p9:p73-had, bpP:p8:coeffs, bpP:p8:laplace, bpP:p9:e-spec, bpP:p9:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p9:p73-had | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:p73-cong@L102-L102 | x^T hat q x<=-c ¦x¦^2 applied to Delta^-1 x
EDGE: bpP:p8:coeffs | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:p73-cong@L102-L102 | Q_h=Delta^-1 hat q Delta^-1, Lambda_i
EDGE: bpP:p8:laplace | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:p73-cong@L102-L102 | continuity of frakt a, frakt b in a
EDGE: bpP:p9:e-spec | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:p73-cong@L102-L102 | an eigenvalue is x^T Q_h x for a unit eigenvector
EDGE: bpP:p9:conv#data | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:p73-cong@L102-L102 | The Euclidean norm, orthonormal/orthogonal matrix convention or Sym_n typing used in this source unit is fixed here.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9+sol-review-P-k
REVIEWER: sol-delta-P-k
LEAN_STATUS: PROVED
LEAN_REF: quad_eigen_le, continuousAt_coercivity, definite (KAM/Planetary/SecularSpectrum/Definiteness.lean)
LEAN_NOTE: audit S9-D PASS WITH NOTES (audit-2, F1 hygiene finding closed; audit-1 FAIL superseded)
NOTE: -

NODE: bpP:p9:local-analytic
KIND: proposition
TITLE: Local analytic spectral decomposition
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:local-analytic@L107-L109
PROOF_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:local-analytic@L110-L115
CONTRACT_ID: bpP:p9:local-analytic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W subset R^m open; M:W->Sym_n real analytic; w0 in W with M(w0) having n distinct eigenvalues (discr!=0)
SOURCE_QUANTIFIERS: m,n,M,w0; then ball W prime
SOURCE_CONCLUSION: exists open ball W prime around w0 and real analytic sigma_j:W prime->R, varrho:W prime->SO(n) with sigma_1<...<sigma_n, M=varrho diag(sigma) varrho^T, sigma_j(w0)=sigma_j^0; spectrum simple on W prime; on a connected open set sigma_j is unique and varrho unique up to column signs (det 1)
CONSTANT_SCOPE: the ball depends on M and w0
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p9:la-ev, stepP:p9:la-adj, stepP:p9:la-vec, stepP:p9:la-so, bpP:p9:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p9:la-ev | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:local-analytic@L111-L111 | proof step Eigenvalues
EDGE: stepP:p9:la-adj | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:local-analytic@L112-L112 | proof step Eigenprojections
EDGE: stepP:p9:la-vec | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:local-analytic@L113-L113 | proof step Eigenvectors
EDGE: stepP:p9:la-so | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:local-analytic@L114-L114 | proof step SO(n) and uniqueness
EDGE: bpP:p9:conv#data | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:local-analytic@L108-L108 | Sym_n
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9
REVIEWER: sol-review-P-k
LEAN_STATUS: PROVED
LEAN_REF: local_analytic (KAM/Planetary/SecularSpectrum/LocalAnalytic/Existence.lean); local_analytic_unique (KAM/Planetary/SecularSpectrum/LocalAnalytic/Unique.lean)
LEAN_NOTE: audit S9-S PASS WITH NOTES
NOTE: -

NODE: stepP:p9:la-ev
KIND: step
TITLE: Eigenvalues
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:la-ev@L111-L111
PROOF_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:la-ev@L111-L111
CONTRACT_ID: stepP:p9:la-ev
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the source premises of bpP:p9:local-analytic: W subset R^m open, M:W->Sym_n real analytic, w0 in W, and n distinct eigenvalues sigma_1^0<...<sigma_n^0 of M(w0); subsequent analytic branches, projections and frames are supplied through DEPS
SOURCE_QUANTIFIERS: j=1..n; w near w0
SOURCE_CONCLUSION: analytic sigma_j(w) with p(w,sigma_j(w))=0, sigma_j(w0)=sigma_j^0; on a ball they are n distinct real roots, hence all eigenvalues of M(w), sigma_1<...<sigma_n, simple spectrum
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p9:e-ift, bpP:p9:e-spec, bpP:p8:e-taylor, bpP:p9:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p9:e-ift | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:la-ev@L111-L111 | analytic implicit function theorem
EDGE: bpP:p9:e-spec | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:la-ev@L111-L111 | det(sI-M)=prod(s-lambda_j)
EDGE: bpP:p8:e-taylor | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:la-ev@L111-L111 | characteristic polynomial composed with analytic M is analytic
EDGE: bpP:p9:conv#data | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:la-ev@L111-L111 | The Euclidean norm, orthonormal/orthogonal matrix convention or Sym_n typing used in this source unit is fixed here.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9+sol-review-P-k
REVIEWER: sol-delta-P-k
LEAN_STATUS: PROVED
LEAN_REF: exists_analytic_root, exists_eigenvalue_branch (KAM/Planetary/SecularSpectrum/LocalAnalytic/Eigenvalues.lean); sorted_strictMono, charpoly_eq_prod_of_roots (KAM/Planetary/SecularSpectrum/LocalAnalytic/Sorted.lean)
LEAN_NOTE: audit S9-S PASS WITH NOTES
NOTE: -

NODE: stepP:p9:la-adj
KIND: step
TITLE: Eigenprojections by the adjugate
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:la-adj@L112-L112
PROOF_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:la-adj@L112-L112
CONTRACT_ID: stepP:p9:la-adj
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the source premises of bpP:p9:local-analytic: W subset R^m open, M:W->Sym_n real analytic, w0 in W, and n distinct eigenvalues sigma_1^0<...<sigma_n^0 of M(w0); subsequent analytic branches, projections and frames are supplied through DEPS
SOURCE_QUANTIFIERS: w in the ball
SOURCE_CONCLUSION: Pi_j(w)=adj(sigma_j I-M)/d_s p(w,sigma_j) equals v_j v_j^T, the orthogonal projection on the sigma_j-eigenspace, real analytic in w
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p9:e-spec, stepP:p9:la-ev, bpP:p8:e-taylor, bpP:p9:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p9:e-spec | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:la-adj@L112-L112 | orthonormal eigenbasis
EDGE: stepP:p9:la-ev | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:la-adj@L112-L112 | analytic simple eigenvalues sigma_j(w), d_s p!=0
EDGE: bpP:p8:e-taylor | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:la-adj@L112-L112 | analytic composition: adjugate polynomial in analytic entries
EDGE: bpP:p9:conv#data | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:la-adj@L112-L112 | The Euclidean norm, orthonormal/orthogonal matrix convention or Sym_n typing used in this source unit is fixed here.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9+sol-review-P-k
REVIEWER: sol-delta-P-k
LEAN_STATUS: PROVED
LEAN_REF: eigProj (KAM/Planetary/SecularSpectrum/LocalAnalytic/Projection.lean); analyticAt_eigProj (KAM/Planetary/SecularSpectrum/LocalAnalytic/Analytic.lean)
LEAN_NOTE: audit S9-S PASS WITH NOTES
NOTE: -

NODE: stepP:p9:la-vec
KIND: step
TITLE: Eigenvectors
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:la-vec@L113-L113
PROOF_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:la-vec@L113-L113
CONTRACT_ID: stepP:p9:la-vec
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the source premises of bpP:p9:local-analytic: W subset R^m open, M:W->Sym_n real analytic, w0 in W, and n distinct eigenvalues sigma_1^0<...<sigma_n^0 of M(w0); subsequent analytic branches, projections and frames are supplied through DEPS
SOURCE_QUANTIFIERS: j
SOURCE_CONCLUSION: analytic orthonormal eigenvectors v_j(w)=Pi_j e_k/sqrt(Pi_j,kk) near w0 for sigma_j(w)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p9:la-adj, stepP:p9:la-ev, bpP:p9:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p9:la-adj | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:la-vec@L113-L113 | Pi_j analytic rank-one projection
EDGE: stepP:p9:la-ev | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:la-vec@L113-L113 | distinct eigenvalues give orthogonality
EDGE: bpP:p9:conv#data | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:la-vec@L113-L113 | The Euclidean norm, orthonormal/orthogonal matrix convention or Sym_n typing used in this source unit is fixed here.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9+sol-review-P-k
REVIEWER: sol-delta-P-k
LEAN_STATUS: PROVED
LEAN_REF: eigFrame (KAM/Planetary/SecularSpectrum/LocalAnalytic/Frame.lean); analyticAt_eigFrame (KAM/Planetary/SecularSpectrum/LocalAnalytic/Analytic.lean)
LEAN_NOTE: audit S9-S PASS WITH NOTES
NOTE: -

NODE: stepP:p9:la-so
KIND: step
TITLE: $SO(n)$ and uniqueness
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:la-so@L114-L114
PROOF_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:la-so@L114-L114
CONTRACT_ID: stepP:p9:la-so
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the source premises of bpP:p9:local-analytic: W subset R^m open, M:W->Sym_n real analytic, w0 in W, and n distinct eigenvalues sigma_1^0<...<sigma_n^0 of M(w0); subsequent analytic branches, projections and frames are supplied through DEPS
SOURCE_QUANTIFIERS: the fixed data m,n,W,M,w0 of local-analytic; w in the chosen connected ball; the ordered branches and frame constructed by the preceding steps
SOURCE_CONCLUSION: varrho in SO(n) after flipping v_1 if needed; uniqueness of sigma_j (continuous root, ordering) and of varrho up to signs
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p9:la-vec, bpP:p9:e-ift, stepP:p9:la-ev, bpP:p9:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p9:la-vec | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:la-so@L114-L114 | orthonormal frame v_j
EDGE: bpP:p9:e-ift | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:la-so@L114-L114 | uniqueness of the continuous root
EDGE: stepP:p9:la-ev | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:la-so@L114-L114 | ordering and simplicity
EDGE: bpP:p9:conv#data | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:la-so@L114-L114 | The Euclidean norm, orthonormal/orthogonal matrix convention or Sym_n typing used in this source unit is fixed here.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9+sol-review-P-k
REVIEWER: sol-delta-P-k
LEAN_STATUS: PROVED
LEAN_REF: local_analytic (KAM/Planetary/SecularSpectrum/LocalAnalytic/Existence.lean); local_analytic_unique (KAM/Planetary/SecularSpectrum/LocalAnalytic/Unique.lean)
LEAN_NOTE: audit S9-S PASS WITH NOTES
NOTE: -

NODE: bpP:p9:lift
KIND: proposition
TITLE: Symplectic lift of a $\Lambda$-dependent rotation
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:lift@L117-L122
PROOF_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:lift@L123-L132
CONTRACT_ID: bpP:p9:lift
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W subset R^n open (actions); varrho:W->SO(n) real analytic; chart form Omega_chart=dLambda^dlambda+deta^dxi; Phi_varrho(lambda,Lambda,xi,eta)=(lambda tilde,Lambda,varrho^T xi,varrho^T eta), lambda tilde_l=lambda_l-eta^T(d_l varrho)varrho^T xi
SOURCE_QUANTIFIERS: n, W, varrho; then points (lambda,Lambda,xi,eta); c in R^n
SOURCE_CONCLUSION: Phi_varrho is a real analytic diffeomorphism of R^n x W x R^n x R^n onto itself with the explicit inverse, symplectic Phi^*Omega_chart=Omega_chart (a 1-chart in the sense of Definition chart), Phi(lambda+c,...)=Phi+(c,0,0,0), preserves Lambda and the Euclidean norms of xi, eta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p9:lift-bij, stepP:p9:lift-anti, stepP:p9:lift-form, stepP:p9:lift-mc, stepP:p9:lift-concl, bpP:p1:chart, bpP:p9:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p9:lift-bij | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:lift@L124-L124 | proof step Bijectivity
EDGE: stepP:p9:lift-anti | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:lift@L125-L125 | proof step Antisymmetry
EDGE: stepP:p9:lift-form | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:lift@L126-L126 | proof step Pull-back computation
EDGE: stepP:p9:lift-mc | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:lift@L130-L130 | proof step Maurer-Cartan
EDGE: stepP:p9:lift-concl | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:lift@L131-L131 | proof step Conclusion
EDGE: bpP:p1:chart | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:lift@L120-L120 | 1-chart in the sense of Definition chart
EDGE: bpP:p9:conv#data | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:lift@L120-L120 | The Euclidean norm, orthonormal/orthogonal matrix convention or Sym_n typing used in this source unit is fixed here.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9+sol-review-P-k
REVIEWER: sol-delta-P-k
LEAN_STATUS: PROVED
LEAN_REF: lift (KAM/Planetary/SecularSpectrum/Lift.lean)
LEAN_NOTE: audit S9-L PASS WITH NOTES
NOTE: edge to bpP:p7:product-chart deleted: the statement only names the form Omega_chart, which it writes out; the lift does not use the chart theorem

NODE: stepP:p9:lift-bij
KIND: step
TITLE: Bijectivity
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:lift-bij@L124-L124
PROOF_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:lift-bij@L124-L124
CONTRACT_ID: stepP:p9:lift-bij
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the source premises of bpP:p9:lift: W subset R^n open and varrho:W->SO(n) real analytic, with the explicitly defined Phi_varrho and form dLambda^dlambda+deta^dxi; H_l and Omega_l denote the local definitions of L124; inverse and differential identities are supplied through DEPS
SOURCE_QUANTIFIERS: (lambda,Lambda,xi,eta)
SOURCE_CONCLUSION: inverse xi=varrho xi tilde, eta=varrho eta tilde, lambda_l=lambda tilde_l+H_l; all maps analytic; commutes with angle translations since lambda tilde-lambda is independent of lambda
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9+sol-review-P-k
REVIEWER: sol-delta-P-k
LEAN_STATUS: PROVED
LEAN_REF: liftInv_liftMap_of_isSO, liftMap_liftInv_of_isSO, liftMap_add_append (KAM/Planetary/SecularSpectrum/Lift/Basic.lean); analyticAt_liftMap (KAM/Planetary/SecularSpectrum/Lift/Analytic.lean)
LEAN_NOTE: audit S9-L PASS WITH NOTES; named lift-bij
NOTE: -

NODE: stepP:p9:lift-anti
KIND: step
TITLE: Antisymmetry
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:lift-anti@L125-L125
PROOF_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:lift-anti@L125-L125
CONTRACT_ID: stepP:p9:lift-anti
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the source premises of bpP:p9:lift: W subset R^n open and varrho:W->SO(n) real analytic, with the explicitly defined Phi_varrho and form dLambda^dlambda+deta^dxi; H_l and Omega_l denote the local definitions of L124; inverse and differential identities are supplied through DEPS
SOURCE_QUANTIFIERS: l
SOURCE_CONCLUSION: Omega_l^T=-Omega_l; d varrho=varrho sum Omega_l dLambda_l, d varrho^T=-sum Omega_l varrho^T dLambda_l
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p9:lift-bij
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p9:lift-bij | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:lift-anti@L125-L125 | Omega_l:=varrho^T d_l varrho is the local definition made at L124.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9+sol-review-P-k
REVIEWER: sol-delta-P-k
LEAN_STATUS: PROVED
LEAN_REF: lift (KAM/Planetary/SecularSpectrum/Lift.lean)
LEAN_NOTE: local to PROVED parent lift (ruling 01:20 (b)); audit S9-L confirms (docs/tracks/P/audits/S9-L-audit-1.md:63)
NOTE: -

NODE: stepP:p9:lift-form
KIND: step
TITLE: Pull-back computation
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:lift-form@L126-L129
PROOF_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:lift-form@L126-L129
CONTRACT_ID: stepP:p9:lift-form
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the source premises of bpP:p9:lift: W subset R^n open and varrho:W->SO(n) real analytic, with the explicitly defined Phi_varrho and form dLambda^dlambda+deta^dxi; H_l and Omega_l denote the local definitions of L124; inverse and differential identities are supplied through DEPS
SOURCE_QUANTIFIERS: the fixed data n,W,varrho of lift; points (lambda,Lambda,xi,eta) with Lambda in W; l,m in {1,...,n}
SOURCE_CONCLUSION: d eta^T^d xi=d eta tilde^T^d xi tilde+sum_l(d eta tilde^T Omega_l xi tilde+eta tilde^T Omega_l d xi tilde)^dLambda_l-sum eta tilde^T Omega_l Omega_m xi tilde dLambda_l^dLambda_m; equals d eta tilde^d xi tilde+sum dH_l^dLambda_l-sum eta tilde^T(d_m Omega_l+Omega_m Omega_l) xi tilde dLambda_m^dLambda_l
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p9:lift-bij, stepP:p9:lift-anti
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p9:lift-bij | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:lift-form@L126-L126 | substitution xi=varrho xi tilde, eta=varrho eta tilde and H_l
EDGE: stepP:p9:lift-anti | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:lift-form@L128-L128 | varrho^T d varrho=sum Omega_l dLambda_l, d varrho^T varrho=-sum Omega_l dLambda_l
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9+sol-review-P-k
REVIEWER: sol-delta-P-k
LEAN_STATUS: PROVED
LEAN_REF: lift (KAM/Planetary/SecularSpectrum/Lift.lean)
LEAN_NOTE: local to PROVED parent lift (ruling 01:20 (b)); audit S9-L confirms (docs/tracks/P/audits/S9-L-audit-1.md:78)
NOTE: -

NODE: stepP:p9:lift-mc
KIND: step
TITLE: Maurer--Cartan
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:lift-mc@L130-L130
PROOF_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:lift-mc@L130-L130
CONTRACT_ID: stepP:p9:lift-mc
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the source premises of bpP:p9:lift: W subset R^n open and varrho:W->SO(n) real analytic, with the explicitly defined Phi_varrho and form dLambda^dlambda+deta^dxi; H_l and Omega_l denote the local definitions of L124; inverse and differential identities are supplied through DEPS
SOURCE_QUANTIFIERS: l,m
SOURCE_CONCLUSION: d_m Omega_l+Omega_m Omega_l=varrho^T d_m d_l varrho is symmetric in (m,l), so the last sum vanishes against dLambda_m^dLambda_l
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p9:lift-anti, stepP:p9:lift-form, stepP:p9:lift-bij
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p9:lift-anti | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:lift-mc@L130-L130 | d_m varrho^T=-Omega_m varrho^T
EDGE: stepP:p9:lift-form | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:lift-mc@L130-L130 | the remaining sum to be killed
EDGE: stepP:p9:lift-bij | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:lift-mc@L130-L130 | The differentiation of Omega_l uses its defining formula Omega_l=varrho^T partial_l varrho, introduced at L124
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9+sol-delta-P-k
REVIEWER: sol-delta2-P-t
LEAN_STATUS: PROVED
LEAN_REF: lift (KAM/Planetary/SecularSpectrum/Lift.lean)
LEAN_NOTE: local to PROVED parent lift (ruling 01:20 (b)); audit S9-L confirms (docs/tracks/P/audits/S9-L-audit-1.md:78)
NOTE: -

NODE: stepP:p9:lift-concl
KIND: step
TITLE: Conclusion
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:lift-concl@L131-L131
PROOF_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:lift-concl@L131-L131
CONTRACT_ID: stepP:p9:lift-concl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the source premises of bpP:p9:lift: W subset R^n open and varrho:W->SO(n) real analytic, with the explicitly defined Phi_varrho and form dLambda^dlambda+deta^dxi; H_l and Omega_l denote the local definitions of L124; inverse and differential identities are supplied through DEPS
SOURCE_QUANTIFIERS: the fixed data n,W,varrho of lift; every point of R^n x W x R^n x R^n and tangent vectors for the pull-back identity
SOURCE_CONCLUSION: d eta^T^d xi=d eta tilde^T^d xi tilde-sum dLambda_l^dH_l, hence Phi^*Omega_chart=Omega_chart; Euclidean norms preserved since varrho orthogonal
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p9:lift-form, stepP:p9:lift-mc, stepP:p9:lift-bij, bpP:p9:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p9:lift-form | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:lift-concl@L131-L131 | pull-back of d eta^d xi
EDGE: stepP:p9:lift-mc | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:lift-concl@L131-L131 | vanishing of the dLambda^dLambda terms
EDGE: stepP:p9:lift-bij | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:lift-concl@L131-L131 | definition lambda tilde=lambda-H and norm preservation
EDGE: bpP:p9:conv#data | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:lift-concl@L131-L131 | The Euclidean norm, orthonormal/orthogonal matrix convention or Sym_n typing used in this source unit is fixed here.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9+sol-review-P-k
REVIEWER: sol-delta-P-k
LEAN_STATUS: PROVED
LEAN_REF: lift (KAM/Planetary/SecularSpectrum/Lift.lean)
LEAN_NOTE: local to PROVED parent lift (ruling 01:20 (b)); audit S9-L confirms (docs/tracks/P/audits/S9-L-audit-1.md:42)
NOTE: -

NODE: bpP:p9:diagonalize
KIND: theorem
TITLE: Diagonalisation and the frozen Birkhoff data
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:diagonalize@L134-L147
PROOF_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:diagonalize@L148-L153
CONTRACT_ID: bpP:p9:diagonalize
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the situation of bpP:p8:perturbation-analytic and bpP:p8:quadratic-form with n>=2; W subset {Lambda: a(Lambda) increasing} open; Q_h(Lambda) has simple spectrum on W; sigma_j, varrho the analytic functions of bpP:p9:local-analytic on W (global labelling if W is connected)
SOURCE_QUANTIFIERS: data of conv#data (Part 8); W; then (xi tilde,eta tilde) with (xi,Lambda,eta)=(varrho xi tilde,Lambda,varrho eta tilde); mu>0
SOURCE_CONCLUSION: (a) xi^T Q_h xi+eta^T Q_h eta=sum sigma_j(xi tilde_j^2+eta tilde_j^2)=sum Omega_j R tilde_j with Omega_j=2 sigma_j<0, R tilde_j=(eta tilde_j^2+xi tilde_j^2)/2; (b) for the matched pairs (S,hat f) the average of hat f o Phi^-1 equals S(Lambda,varrho xi tilde,varrho eta tilde)=C_0+[delta]+sum Omega_j R tilde_j+O(¦(xi tilde,eta tilde)¦^4) locally uniformly in Lambda in W, on the set where (xi,Lambda,eta)=(varrho xi tilde,Lambda,varrho eta tilde) belongs to N_R(rho_*), [delta]=0 (fix) or delta(Lambda) (mov); H^Psi transformed by Phi^-1 is h(Lambda)+mu hat f o Phi^-1; (c) with (I,p,q)=(Lambda,eta tilde,xi tilde), P_0=C_0(+delta), Omega_j(mu,I)=2 sigma_j(a(I)), R_j=(p_j^2+q_j^2)/2 the zeroth and first order terms of HasBirkhoff for P=hat f o Phi^-1 are those of (b); beta and clause (i) not treated; domain condition sqrt n delta_0<=rho_* and ¦Lambda-Lambda*¦_inf<rho_*; (d) Psi o Phi^-1 is a symplectic chart of Part 1 satisfying (Q1)-(Q2) of the torus transport theorem whenever Psi does
CONSTANT_SCOPE: rho_*, a, Q_h as in Part 8; sigma_j, varrho depend on Lambda only (not on mu)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p9:d-a, stepP:p9:d-b, stepP:p9:d-c, stepP:p9:d-d, bpP:p8:perturbation-analytic, bpP:p8:quadratic-form, bpP:p9:local-analytic, bpP:p9:lift, bpP:p8:identification, bpP:p0:birkhoff#HasSecularBirkhoffForm, bpP:p8:conv#data, bpP:p1:chart, bpP:p1:torus-transport, bpP:p9:conv#data, bpP:p8:rho, bpP:p8:coeffs
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p9:d-a | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:diagonalize@L149-L149 | proof step (a)
EDGE: stepP:p9:d-b | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:diagonalize@L150-L150 | proof step (b)
EDGE: stepP:p9:d-c | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:diagonalize@L151-L151 | proof step (c)
EDGE: stepP:p9:d-d | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:diagonalize@L152-L152 | proof step (d)
EDGE: bpP:p8:perturbation-analytic | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:diagonalize@L135-L135 | situation, rho_*, matched pairs (S,hat f)
EDGE: bpP:p8:quadratic-form | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:diagonalize@L135-L135 | situation; Q_h and the expansion of S_fix
EDGE: bpP:p9:local-analytic | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:diagonalize@L135-L135 | sigma_j, varrho analytic functions
EDGE: bpP:p9:lift | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:diagonalize@L137-L137 | the rotation lift Phi_varrho and (xi tilde,eta tilde)
EDGE: bpP:p8:identification | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:diagonalize@L141-L141 | [delta]=delta(Lambda) for mov
EDGE: bpP:p0:birkhoff#HasSecularBirkhoffForm | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:diagonalize@L142-L142 | frozen Omega_j, R_j, P_0 of HasBirkhoff
EDGE: bpP:p8:conv#data | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:diagonalize@L142-L142 | dictionary (I,p,q)=(Lambda,eta,xi) and N_R(rho_*)
EDGE: bpP:p1:chart | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:diagonalize@L143-L143 | symplectic chart of Part 1
EDGE: bpP:p1:torus-transport | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:diagonalize@L143-L143 | lattice compatibility (Q1)-(Q2) and applicability of torus transport
EDGE: bpP:p9:conv#data | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:diagonalize@L135-L135 | conventions of Part 9
EDGE: bpP:p8:rho | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:diagonalize@L141-L141 | The named secular polydisc constants and rho_* enter the asserted domain.
EDGE: bpP:p8:coeffs | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:diagonalize@L135-L135 | Q_h(a) and its real analytic dependence are the secular coefficients defined here.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9+sol-delta-P-k
REVIEWER: sol-delta2-P-t
LEAN_STATUS: PROVED
LEAN_REF: diagonalize, diagonalize_mem_realDisc (KAM/Planetary/SecularSpectrum/Diagonalize.lean); diagonalize_transport, diagonalize_period_one (KAM/Planetary/SecularSpectrum/Transport.lean)
LEAN_NOTE: composite of audits S9-Q PASS WITH NOTES (round 2; clauses a-c) + S9-T PASS WITH NOTES (clause d); SOURCE_GAP N2 (audit S9-T-1): blueprint L143/L152 Cartesian lift-only lattice wording is repaired explicitly in the signed statement (Psi o liftInv R o polarMap o phaseCast, period conversion omega/(2 pi)); proved under that repair
NOTE: edges deleted: bpP:p8:same-jets (pointer: beta and clause (i) are treated in Part 11b), bpP:p8:factor-half (remark, source provenance). The sourcegap at L146 (angle correction of the rotation) is bridged by bpP:p9:lift and step d-b SOURCE_GAP: L143/L152 assert the lattice compatibility of the period-one torus-transport theorem using 2 pi shifts of the physical chart. Part 1 defines iota_k using integer shifts, whereas this proof checks shifts by 2 pi m. Applying that theorem directly still needs a named period conversion (as in Part 1 period-convert/cyl-pipeline), with its torus and frequency hypotheses. The source supplies the valid 2 pi shift calculation but does not perform this conversion here; no additional premise or conversion proof is inserted by the graph.

NODE: stepP:p9:d-a
KIND: step
TITLE: (a)
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-a@L149-L149
PROOF_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-a@L149-L149
CONTRACT_ID: stepP:p9:d-a
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the source premises of bpP:p9:diagonalize: the Part 8 perturbation and quadratic-form setting with n>=2, W open in the increasing-axis action domain, and given analytic sigma_j,varrho on W with Q_h=varrho diag(sigma)varrho^T and simple increasingly labelled spectrum; derived negativity, lift identities and average bounds are supplied through DEPS
SOURCE_QUANTIFIERS: xi,eta in R^n
SOURCE_CONCLUSION: xi^T Q_h xi=sum sigma_j xi tilde_j^2, similarly eta; sigma_j(xi tilde_j^2+eta tilde_j^2)=2 sigma_j R tilde_j; Omega_j=2 sigma_j<0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p9:definite, bpP:p9:local-analytic, bpP:p9:lift, bpP:p8:coeffs
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p9:definite | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-a@L149-L149 | negativity of sigma_j
EDGE: bpP:p9:local-analytic | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-a@L149-L149 | Q_h=varrho diag(sigma) varrho^T
EDGE: bpP:p9:lift | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-a@L149-L149 | xi tilde=varrho^T xi, eta tilde=varrho^T eta
EDGE: bpP:p8:coeffs | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-a@L149-L149 | Q_h
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9+sol-review-P-k
REVIEWER: sol-delta-P-k
LEAN_STATUS: PROVED
LEAN_REF: diagonalize, rotDiag_quad_conj, rotDiag_quad_rot (KAM/Planetary/SecularSpectrum/Diagonalize.lean)
LEAN_NOTE: audit S9-Q PASS WITH NOTES (round 2); diagonalize conjuncts 1,3
NOTE: -

NODE: stepP:p9:d-b
KIND: step
TITLE: (b)
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-b@L150-L150
PROOF_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-b@L150-L150
CONTRACT_ID: stepP:p9:d-b
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the source premises of bpP:p9:diagonalize: the Part 8 perturbation and quadratic-form setting with n>=2, W open in the increasing-axis action domain, and given analytic sigma_j,varrho on W with Q_h=varrho diag(sigma)varrho^T and simple increasingly labelled spectrum; derived negativity, lift identities and average bounds are supplied through DEPS; (S,hat f) is one of the two matched pairs, and the rotated point lies in N_R(rho_*)
SOURCE_QUANTIFIERS: (S,hat f) matched pair; (xi,Lambda,eta) in N_R(rho_*)
SOURCE_CONCLUSION: average over lambda tilde of hat f o Phi^-1 equals S(Lambda,varrho xi tilde,varrho eta tilde)=C_0+[delta]+sum Omega_j R tilde_j+O(¦(xi tilde,eta tilde)¦^4); H^Psi o Phi^-1=h(Lambda)+mu hat f o Phi^-1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p9:lift, bpP:p8:perturbation-analytic, bpP:p8:e-diff, bpP:p8:quadratic-form, bpP:p8:identification, stepP:p9:d-a, bpP:p7:product-chart, bpP:p9:conv#data, bpP:p8:rho, bpP:p8:conv#data, bpP:p8:coeffs
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p9:lift | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-b@L150-L150 | explicit inverse with H independent of lambda tilde; Phi preserves Lambda and norms
EDGE: bpP:p8:perturbation-analytic | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-b@L150-L150 | (b): hat f continuous and 2pi-periodic
EDGE: bpP:p8:e-diff | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-b@L150-L150 | translation invariance of the average of a periodic function
EDGE: bpP:p8:quadratic-form | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-b@L150-L150 | S_fix=C_0+quadratic form+O(4)
EDGE: bpP:p8:identification | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-b@L150-L150 | S_mov=S_fix+delta
EDGE: stepP:p9:d-a | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-b@L150-L150 | quadratic part in the rotated variables
EDGE: bpP:p7:product-chart | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-b@L150-L150 | (b),(c): H^Psi=h+mu f o Psi, h depends on Lambda only
EDGE: bpP:p9:conv#data | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-b@L150-L150 | The Euclidean norm, orthonormal/orthogonal matrix convention or Sym_n typing used in this source unit is fixed here.
EDGE: bpP:p8:rho | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-b@L150-L150 | The named secular polydisc constants and rho_* enter the asserted domain.
EDGE: bpP:p8:conv#data | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-b@L150-L150 | The normalized secular average, chart order and dictionary (I,p,q)=(Lambda,eta,xi) are used here.
EDGE: bpP:p8:coeffs | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-b@L150-L150 | The displayed expansion uses C_0, defined by the secular coefficient package
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9+sol-delta-P-k
REVIEWER: sol-delta2-P-t
LEAN_STATUS: PROVED
LEAN_REF: diagonalize, rotDiag_avg_shift, rotDiag_avg_lift, rotDiag_liftInv_assemble (KAM/Planetary/SecularSpectrum/Diagonalize.lean); diagonalize_period_one (KAM/Planetary/SecularSpectrum/Transport.lean)
LEAN_NOTE: composite of audits S9-Q PASS WITH NOTES (secular average) + S9-T PASS WITH NOTES (Hamiltonian/chart transport)
NOTE: -

NODE: stepP:p9:d-c
KIND: step
TITLE: (c)
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-c@L151-L151
PROOF_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-c@L151-L151
CONTRACT_ID: stepP:p9:d-c
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the source premises of bpP:p9:diagonalize: the Part 8 perturbation and quadratic-form setting with n>=2, W open in the increasing-axis action domain, and given analytic sigma_j,varrho on W with Q_h=varrho diag(sigma)varrho^T and simple increasingly labelled spectrum; derived negativity, lift identities and average bounds are supplied through DEPS; delta_0>0 and the oscillator-disc guards and action-neighborhood guard of clause (c)
SOURCE_QUANTIFIERS: delta_0>0 with xi tilde_j^2+eta tilde_j^2<delta_0^2
SOURCE_CONCLUSION: the zeroth and first order terms of HasBirkhoff for P=hat f o Phi^-1 are P_0=C_0(+delta) and Omega_j R_j; (xi,Lambda,eta) in N_R(rho_*) if sqrt n delta_0<=rho_* and ¦Lambda-Lambda*¦_inf<rho_*
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p9:d-a, stepP:p9:d-b, bpP:p0:birkhoff#HasSecularBirkhoffForm, bpP:p9:conv#data, bpP:p8:perturbation-analytic, bpP:p8:rho, bpP:p8:conv#data, bpP:p8:coeffs
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p9:d-a | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-c@L151-L151 | quadratic part
EDGE: stepP:p9:d-b | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-c@L151-L151 | average and expansion
EDGE: bpP:p0:birkhoff#HasSecularBirkhoffForm | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-c@L151-L151 | terms of HasBirkhoff read off
EDGE: bpP:p9:conv#data | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-c@L151-L151 | norm comparison
EDGE: bpP:p8:perturbation-analytic | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-c@L151-L151 | rho_*, N_R(rho_*)
EDGE: bpP:p8:rho | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-c@L151-L151 | The named secular polydisc constants and rho_* enter the asserted domain.
EDGE: bpP:p8:conv#data | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-c@L151-L151 | The normalized secular average, chart order and dictionary (I,p,q)=(Lambda,eta,xi) are used here.
EDGE: bpP:p8:coeffs | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-c@L151-L151 | The frozen dictionary identifies P_0=C_0(+delta), using C_0 from the secular coefficient package
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9+sol-delta-P-k
REVIEWER: sol-delta2-P-t
LEAN_STATUS: PROVED
LEAN_REF: diagonalize, diagonalize_mem_realDisc, rotDiag_length2_mulVec (KAM/Planetary/SecularSpectrum/Diagonalize.lean)
LEAN_NOTE: audit S9-Q PASS WITH NOTES (round 2; round-1 F1 sqrt(n) domain implication closed by diagonalize_mem_realDisc)
NOTE: -

NODE: stepP:p9:d-d
KIND: step
TITLE: (d)
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-d@L152-L152
PROOF_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-d@L152-L152
CONTRACT_ID: stepP:p9:d-d
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the source premises of bpP:p9:diagonalize: the Part 8 perturbation and quadratic-form setting with n>=2, W open in the increasing-axis action domain, and given analytic sigma_j,varrho on W with Q_h=varrho diag(sigma)varrho^T and simple increasingly labelled spectrum; derived negativity, lift identities and average bounds are supplied through DEPS; the lattice properties of Psi are the conditional premise of clause (d), with the source 2 pi angle convention
SOURCE_QUANTIFIERS: the fixed data and analytic rotation of diagonalize; z,z prime in the preimage of O_n and lattice indices k,m for the two compatibility implications
SOURCE_CONCLUSION: Psi o Phi^-1 is a symplectic chart (pull-back of Omega_cart is Omega_chart), satisfies (Q1) and (Q2) whenever Psi does, so torus transport applies
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p9:lift, bpP:p7:product-chart, bpP:p1:chart, bpP:p1:torus-transport
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p9:lift | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-d@L152-L152 | Phi^*Omega_chart=Omega_chart; shift compatibility; injectivity
EDGE: bpP:p7:product-chart | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-d@L152-L152 | (a): Psi chart with lattice property
EDGE: bpP:p1:chart | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-d@L152-L152 | The displayed pull-back identity identifies the composition as a 1-chart under this definition.
EDGE: bpP:p1:torus-transport | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:d-d@L152-L152 | (Q1)-(Q2)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9+sol-review-P-k
REVIEWER: sol-delta-P-k
LEAN_STATUS: PROVED
LEAN_REF: diagonalize_transport, diagonalize_period_one, rotatedPhysicalChart, rotatedDomain (KAM/Planetary/SecularSpectrum/Transport.lean)
LEAN_NOTE: audit S9-T PASS WITH NOTES; SOURCE_GAP N2 (audit S9-T-1): blueprint L143/L152 Cartesian lift-only lattice wording is repaired explicitly in the signed statement (Psi o liftInv R o polarMap o phaseCast, period conversion omega/(2 pi)); proved under that repair
NOTE: SOURCE_GAP: L143/L152 assert the lattice compatibility of the period-one torus-transport theorem using 2 pi shifts of the physical chart. Part 1 defines iota_k using integer shifts, whereas this proof checks shifts by 2 pi m. Applying that theorem directly still needs a named period conversion (as in Part 1 period-convert/cyl-pipeline), with its torus and frequency hypotheses. The source supplies the valid 2 pi shift calculation but does not perform this conversion here; no additional premise or conversion proof is inserted by the graph.

NODE: bpP:p9:dict
KIND: claim
TITLE: Dictionary: Fej04r, CP09/CP10, frozen
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:dict@L155-L160
PROOF_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:dict@L155-L160
CONTRACT_ID: bpP:p9:dict
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: frozen Omega_j multiplies R_j=(p_j^2+q_j^2)/2 (Definition birkhoff); S=C_0+sum sigma_j(xi tilde_j^2+eta tilde_j^2); sigma_j eigenvalues of the halved Q_h
SOURCE_QUANTIFIERS: n>=2 (item 4: n=1); j
SOURCE_CONCLUSION: Omega_j=2 sigma_j with sigma_j the eigenvalues of the halved Q_h; Omega is the eigenvalue list of 2 Q_h; all negative; CP10 (8) is insensitive to the overall sign; index and labelling conventions; n=1: Q_h=0, Omega_1=0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p9:diagonalize, bpP:p9:definite, bpP:p8:coeffs, bpP:p0:birkhoff#HasSecularBirkhoffForm
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p9:diagonalize | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:dict@L156-L156 | S=C_0+sum sigma_j(...)=C_0+sum 2 sigma_j R tilde_j
EDGE: bpP:p9:definite | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:dict@L156-L156 | all eigenvalues negative
EDGE: bpP:p8:coeffs | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:dict@L156-L156 | the halved Q_h of Definition coeffs
EDGE: bpP:p0:birkhoff#HasSecularBirkhoffForm | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:dict@L156-L156 | frozen Omega_j, R_j
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9+sol-delta-P-k
REVIEWER: sol-delta2-P-t
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: kept as claim: Part 10 L192 cites it for the dictionary Omega_j=2 sigma_j; if the P-p10 extractor finds no consumer, exclude it. Edge to bpP:p8:factor-half deleted (provenance/erratum remark)

NODE: bpP:p9:good
KIND: definition
TITLE: Non-resonance up to order four; the function $\Phi_4$
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:good@L164-L171
PROOF_SOURCE: -
CONTRACT_ID: bpP:p9:good
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K_4={k in Z^n: 0<¦k¦_1<=4}; sigma in R^n; a in {a_1<...<a_n}
SOURCE_QUANTIFIERS: n; sigma; a
SOURCE_CONCLUSION: defines NR_4(sigma): sigma_j pairwise distinct and k.sigma!=0 for all k in K_4; R_k(sigma)=prod_{pi in S_n} sum_j k_j sigma_pi(j); D(sigma)=prod_{j<l}(sigma_j-sigma_l)^2; Phi_4(sigma)=D(sigma) prod_{k in K_4} R_k(sigma); Phi_4(a):=Phi_4(sigma(a)) for the eigenvalues of Q_h(a) in any order; NR_4(sigma) iff NR_4(Omega) for Omega=2 sigma, and the quantitative bound ¦Omega.k¦>=alpha>0 for k in K_4 holds uniformly on every compact subset of the non-resonant locus by continuity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p8:coeffs, bpP:p9:e-spec
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p8:coeffs | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:good@L169-L169 | Q_h(a)
EDGE: bpP:p9:e-spec | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:good@L169-L169 | eigenvalues sigma(a) of the symmetric matrix Q_h(a)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9+sol-review-P-k
REVIEWER: sol-delta-P-k
LEAN_STATUS: PROVED
LEAN_REF: k4, nr4, discriminant, k4_finite, good, good_comp, good_ne_zero_iff (KAM/Planetary/SecularSpectrum/GoodPolynomial.lean)
LEAN_NOTE: audit S9-G PASS WITH NOTES; definitions k4,nr4,discriminant,good plus nr4 characterisation and permutation invariance; compact uniformity clause not part of this node's Lean (handled by consumers)
NOTE: -

NODE: bpP:p9:good-set
KIND: proposition
TITLE: The good set
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:good-set@L173-L179
PROOF_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:good-set@L180-L184
CONTRACT_ID: bpP:p9:good-set
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Phi_4 of Definition good; (c) A subset {a_1<...<a_n} open and connected
SOURCE_QUANTIFIERS: n; a; (c) A
SOURCE_CONCLUSION: (a) Phi_4 symmetric polynomial in sigma, a->Phi_4(a) polynomial in the coefficients of det(sI-Q_h(a)), real analytic on {a_1<...<a_n}, independent of labelling; (b) Phi_4(a)!=0 iff NR_4(sigma(a)), then simple spectrum, Omega_j=2 sigma_j!=0 and local-analytic, diagonalize apply on a ball around a; (c) either Phi_4=0 on A or G={Phi_4!=0} is open, dense and of full measure in A; one good point gives open dense full-measure set with analytic distinct eigenvalues and non-resonance, uniform on compacts of G
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p9:gs-a, stepP:p9:gs-b, stepP:p9:gs-c, bpP:p9:good, bpP:p9:local-analytic, bpP:p9:diagonalize, bpP:p8:coeffs, bpP:p8:perturbation-analytic, bpP:p8:quadratic-form
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p9:gs-a | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:good-set@L181-L181 | proof step (a)
EDGE: stepP:p9:gs-b | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:good-set@L182-L182 | proof step (b)
EDGE: stepP:p9:gs-c | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:good-set@L183-L183 | proof step (c)
EDGE: bpP:p9:good | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:good-set@L175-L175 | Phi_4, NR_4
EDGE: bpP:p9:local-analytic | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:good-set@L176-L176 | Proposition local-analytic applies on a ball
EDGE: bpP:p9:diagonalize | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:good-set@L176-L176 | Theorem diagonalize applies on a ball
EDGE: bpP:p8:coeffs | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:good-set@L175-L175 | Q_h(a) and its real analytic dependence are the secular coefficients defined here.
EDGE: bpP:p8:perturbation-analytic | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:good-set@L176-L176 | These supply the physical perturbation and expansion premises required when diagonalize is invoked on the good patch.
EDGE: bpP:p8:quadratic-form | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:good-set@L176-L176 | These supply the physical perturbation and expansion premises required when diagonalize is invoked on the good patch.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9+sol-review-P-k
REVIEWER: sol-delta-P-k
LEAN_STATUS: PROVED
LEAN_REF: good_set_bundle, two_sigma_ne_zero (KAM/Planetary/SecularSpectrum/GoodSetNodes.lean)
LEAN_NOTE: audit GAP-P9b round 2 PASS WITH NOTES
NOTE: -

NODE: stepP:p9:gs-a
KIND: step
TITLE: (a)
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:gs-a@L181-L181
PROOF_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:gs-a@L181-L181
CONTRACT_ID: stepP:p9:gs-a
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the source setting of bpP:p9:good-set and Definition bpP:p9:good: the physical Q_h(a) and Phi_4,D,R_k,K_4 as defined there, with a in the positive increasing-axis domain; the symmetry and nonvanishing equivalences are conclusions, not extra premises
SOURCE_QUANTIFIERS: a in {a_1<...<a_n}
SOURCE_CONCLUSION: Phi_4 is a symmetric polynomial hence a polynomial in the elementary symmetric polynomials of sigma, i.e. in the coefficients of det(sI-Q_h(a)), which are polynomials in the real analytic entries of Q_h(a): Phi_4(a) real analytic
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p9:e-fts, bpP:p9:e-spec, bpP:p8:coeffs, bpP:p9:good
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p9:e-fts | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:gs-a@L181-L181 | symmetric polynomial is a polynomial in the elementary ones
EDGE: bpP:p9:e-spec | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:gs-a@L181-L181 | charpoly coefficients up to sign are the elementary symmetric polynomials
EDGE: bpP:p8:coeffs | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:gs-a@L181-L181 | Q_h(a) real analytic
EDGE: bpP:p9:good | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:gs-a@L181-L181 | Phi_4, D, R_k
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9+sol-review-P-k
REVIEWER: sol-delta-P-k
LEAN_STATUS: PROVED
LEAN_REF: good_characteristic, good_set, goodPoly_isSymmetric, eval_goodPoly (KAM/Planetary/SecularSpectrum/GoodPolynomial.lean)
LEAN_NOTE: audit S9-G PASS WITH NOTES; symmetric polynomial in charpoly coefficients, real analytic on axes
NOTE: -

NODE: stepP:p9:gs-b
KIND: step
TITLE: (b)
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:gs-b@L182-L182
PROOF_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:gs-b@L182-L182
CONTRACT_ID: stepP:p9:gs-b
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the source setting of bpP:p9:good-set and Definition bpP:p9:good: the physical Q_h(a) and Phi_4,D,R_k,K_4 as defined there, with a in the positive increasing-axis domain; the symmetry and nonvanishing equivalences are conclusions, not extra premises
SOURCE_QUANTIFIERS: a
SOURCE_CONCLUSION: Phi_4(a)!=0 iff NR_4(sigma(a)); simple spectrum (discr=D!=0) by Proposition local-analytic
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p9:good, bpP:p9:local-analytic, bpP:p8:coeffs
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p9:good | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:gs-b@L182-L182 | D, R_k, NR_4, K_4
EDGE: bpP:p9:local-analytic | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:gs-b@L182-L182 | simple spectrum from discr!=0
EDGE: bpP:p8:coeffs | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:gs-b@L182-L182 | Q_h(a) and its real analytic dependence are the secular coefficients defined here.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9+sol-review-P-k
REVIEWER: sol-delta-P-k
LEAN_STATUS: PROVED
LEAN_REF: good_set, good_ne_zero_iff, discriminant_ne_zero_iff (KAM/Planetary/SecularSpectrum/GoodPolynomial.lean)
LEAN_NOTE: audit S9-G PASS WITH NOTES; good!=0 iff nr4 (includes injectivity = simple spectrum); local-analytic branches not claimed here
NOTE: -

NODE: stepP:p9:gs-c
KIND: step
TITLE: (c)
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:gs-c@L183-L183
PROOF_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:gs-c@L183-L183
CONTRACT_ID: stepP:p9:gs-c
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the source setting of bpP:p9:good-set(c): A open and connected in the positive increasing-axis domain, with Phi_4 of bpP:p9:good; in the nonzero branch assume only that Phi_4 is not identically zero; analyticity is established by gs-a, not assumed as an independent input
SOURCE_QUANTIFIERS: A open connected
SOURCE_CONCLUSION: if Phi_4 not identically 0, its zero set is closed, nowhere dense and null; uniformity on compacts of G by continuity of a->sigma(a) and finiteness of K_4
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p9:e-id, stepP:p9:gs-a, bpP:p9:good
ROUTES: stepP:p9:gs-c#roots-route, stepP:p9:gs-c#analytic-route
ROUTE_FOR: -
EDGE: bpP:p9:e-id | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:gs-c@L183-L183 | identity theorem and null zero set
EDGE: stepP:p9:gs-a | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:gs-c@L183-L183 | Phi_4 real analytic
EDGE: bpP:p9:good | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:gs-c@L183-L183 | Phi_4, K_4, the good locus and finiteness of K_4 are used for the compact quantitative bound.
EDGE: stepP:p9:gs-c#roots-route | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:gs-c@L183-L183 | Alternative continuity argument: continuity of roots.
EDGE: stepP:p9:gs-c#analytic-route | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:gs-c@L183-L183 | Alternative continuity argument: locally apply local-analytic.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9+sol-review-P-k
REVIEWER: sol-delta-P-k
LEAN_STATUS: PROVED
LEAN_REF: good_zero_set_small, good_uniform_nonresonance, good_set_bundle (KAM/Planetary/SecularSpectrum/GoodSetNodes.lean)
LEAN_NOTE: audit GAP-P9b round 2 PASS WITH NOTES
NOTE: -

NODE: bpP:p9:n2
KIND: corollary
TITLE: $n=2$: explicit
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:n2@L193-L200
PROOF_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:n2@L201-L204
CONTRACT_ID: bpP:p9:n2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n=2; alpha=a_1/a_2; frakt a=frakt a_12, frakt b=frakt b_12 of Definition coeffs
SOURCE_QUANTIFIERS: a_1<a_2
SOURCE_CONCLUSION: Q_h explicit 2x2 matrix, tr Q_h=-a(1/Lambda_1+1/Lambda_2), det Q_h=(a^2-b^2)/(Lambda_1 Lambda_2)>0, tr^2-4 det>0; eigenvalues sigma_1<sigma_2<0 distinct and real analytic with a global analytic rotation varrho in SO(2) on {a_1<a_2}; NR_4(sigma) iff t=sigma_1/sigma_2 not in {2,3} iff (2 tr^2-9 det)(3 tr^2-16 det)!=0; Phi_4 and R=(2 tr^2-9 det)(3 tr^2-16 det) have the same zero set on {a_1<a_2}; they are not equal up to a nonvanishing factor: at each ratio-2 or ratio-3 resonance its factor occurs to fourth power in Phi_4, so Phi_4 vanishes to higher order; only the nonvanishing equivalence is used, and R is an explicit real analytic function of the axes
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p9:n2-mat, stepP:p9:n2-res, bpP:p8:coeffs, bpP:p9:good, bpP:p9:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p9:n2-mat | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:n2@L202-L202 | proof step Matrix
EDGE: stepP:p9:n2-res | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:n2@L203-L203 | proof step Resonances
EDGE: bpP:p8:coeffs | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:n2@L194-L194 | frakt a_12, frakt b_12, Q_h for n=2
EDGE: bpP:p9:good | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:n2@L198-L198 | NR_4 and Phi_4
EDGE: bpP:p9:conv#data | blueprint-P/parts/p9-secular-spectrum.tex#bpP:p9:n2@L197-L197 | The Euclidean norm, orthonormal/orthogonal matrix convention or Sym_n typing used in this source unit is fixed here.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9+sol-review-P-k
REVIEWER: sol-delta-P-k
LEAN_STATUS: PROVED
LEAN_REF: n2, n2_global_frame (KAM/Planetary/SecularSpectrum/TwoPlanets.lean)
LEAN_NOTE: audit S9-2 PASS WITH NOTES
NOTE: -

NODE: stepP:p9:n2-mat
KIND: step
TITLE: Matrix
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:n2-mat@L202-L202
PROOF_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:n2-mat@L202-L202
CONTRACT_ID: stepP:p9:n2-mat
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the source premises of bpP:p9:n2: n=2 with the positive physical data and 0<a_1<a_2; alpha=a_1/a_2, frakt a=frakt a_12 and frakt b=frakt b_12 of bpP:p8:coeffs; derived determinant, simplicity, negativity and resonance identities are supplied through DEPS
SOURCE_QUANTIFIERS: a_1<a_2
SOURCE_CONCLUSION: Q_h explicit, det=(a^2-b^2)/(Lambda_1 Lambda_2)>0 by Lemma l74, tr^2-4 det>0, global analytic frame varrho=(v1 v2) with v1=w/¦w¦, w=(q_12,sigma_1-q_11), v2=J v1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p8:coeffs, bpP:p9:l74, bpP:p9:e-spec, bpP:p9:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p8:coeffs | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:n2-mat@L202-L202 | hat q, Q_h for n=2 and symmetry a_21=a_12
EDGE: bpP:p9:l74 | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:n2-mat@L202-L202 | a>b (b_{3/2}^(1)>b_{3/2}^(2)) gives det>0
EDGE: bpP:p9:e-spec | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:n2-mat@L202-L202 | eigenvector of the other eigenvalue by symmetry and simple spectrum
EDGE: bpP:p9:conv#data | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:n2-mat@L202-L202 | The Euclidean norm, orthonormal/orthogonal matrix convention or Sym_n typing used in this source unit is fixed here.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9+sol-review-P-k
REVIEWER: sol-delta-P-k
LEAN_STATUS: PROVED
LEAN_REF: n2_global_frame (KAM/Planetary/SecularSpectrum/TwoPlanets.lean)
LEAN_NOTE: audit S9-2 PASS WITH NOTES; global frame via normalized local frames (valid proof-plan variation)
NOTE: -

NODE: stepP:p9:n2-res
KIND: step
TITLE: Resonances
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:n2-res@L203-L203
PROOF_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:n2-res@L203-L203
CONTRACT_ID: stepP:p9:n2-res
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the source premises of bpP:p9:n2: n=2 with the positive physical data and 0<a_1<a_2; alpha=a_1/a_2, frakt a=frakt a_12 and frakt b=frakt b_12 of bpP:p8:coeffs; derived determinant, simplicity, negativity and resonance identities are supplied through DEPS
SOURCE_QUANTIFIERS: k in K_4
SOURCE_CONCLUSION: NR_4(sigma) iff t not in {2,3} iff (2 tr^2-9 det)(3 tr^2-16 det)!=0 (tr^2/det=9/2 at t=2, 16/3 at t=3, t+1/t injective on (1,inf))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p9:definite, stepP:p9:n2-mat, bpP:p9:good
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p9:definite | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:n2-res@L203-L203 | sigma_j<0
EDGE: stepP:p9:n2-mat | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:n2-res@L203-L203 | sigma_1<sigma_2, tr, det
EDGE: bpP:p9:good | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:n2-res@L203-L203 | NR_4, K_4
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p9+sol-review-P-k
REVIEWER: sol-delta-P-k
LEAN_STATUS: PROVED
LEAN_REF: n2 (KAM/Planetary/SecularSpectrum/TwoPlanets.lean)
LEAN_NOTE: audit S9-2 PASS WITH NOTES
NOTE: -

NODE: stepP:p9:gs-c#roots-route
KIND: route
TITLE: Compact uniformity using continuity of roots
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:gs-c@L183-L183
PROOF_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:gs-c@L183-L183
CONTRACT_ID: stepP:p9:gs-c#roots-route
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the source setting of good-set(c); a compact subset of G={a in A:Phi_4(a)!=0}
SOURCE_QUANTIFIERS: fixed physical data; A open connected; compact subset of G; k in K_4
SOURCE_CONCLUSION: the continuous local eigenvalue values and finite set K_4 give a positive uniform lower bound for all nonzero combinations Omega.k on the compact subset
CONSTANT_SCOPE: the positive lower bound depends on the fixed data and chosen compact subset
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p8:coeffs, bpP:p9:good
ROUTES: -
ROUTE_FOR: stepP:p9:gs-c
EDGE: bpP:p8:coeffs | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:gs-c@L183-L183 | Q_h(a) is the real analytic matrix family to which the continuity argument is applied.
EDGE: bpP:p9:good | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:gs-c@L183-L183 | NR_4 excludes zero combinations and K_4 is finite.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: new+sol-review-P-k
REVIEWER: sol-delta-P-k
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: L183 asserts continuity of roots as one alternative. No admitted external or imported source contract in this packet supplies that general theorem. This branch records the asserted bridge; the analytic-route is the explicitly supplied alternative.

NODE: stepP:p9:gs-c#analytic-route
KIND: route
TITLE: Compact uniformity using local analytic eigenvalue branches
STATEMENT_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:gs-c@L183-L183
PROOF_SOURCE: blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:gs-c@L183-L183
CONTRACT_ID: stepP:p9:gs-c#analytic-route
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the source setting of good-set(c); a compact subset of G={a in A:Phi_4(a)!=0}
SOURCE_QUANTIFIERS: fixed physical data; A open connected; compact subset of G; k in K_4
SOURCE_CONCLUSION: the continuous local eigenvalue values and finite set K_4 give a positive uniform lower bound for all nonzero combinations Omega.k on the compact subset
CONSTANT_SCOPE: the positive lower bound depends on the fixed data and chosen compact subset
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p9:local-analytic, bpP:p8:coeffs, bpP:p9:good
ROUTES: -
ROUTE_FOR: stepP:p9:gs-c
EDGE: bpP:p9:local-analytic | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:gs-c@L183-L183 | Local analytic branches imply continuity on the simple-spectrum patch.
EDGE: bpP:p8:coeffs | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:gs-c@L183-L183 | Q_h(a) is the real analytic matrix family to which the continuity argument is applied.
EDGE: bpP:p9:good | blueprint-P/parts/p9-secular-spectrum.tex#stepP:p9:gs-c@L183-L183 | NR_4 excludes zero combinations and K_4 is finite.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: new+sol-review-P-k
REVIEWER: sol-delta-P-k
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The analytic eigenvalue branches are local on the simple-spectrum good set. Finiteness of K_4 and compactness give a positive minimum; no global eigenvector frame is assumed.

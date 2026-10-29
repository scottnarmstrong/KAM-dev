NODE: bpP:p8:e-param
KIND: external
TITLE: Holomorphic parameter integrals
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#bpP:p8:e-param@L26-L26
PROOF_SOURCE: -
CONTRACT_ID: bpP:p8:e-param
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: phi(lambda,w') continuous on [0,2pi]^n x U, U subset C^N open, holomorphic in w' in U for each lambda
SOURCE_QUANTIFIERS: n, N, U, phi
SOURCE_CONCLUSION: w' -> int phi dlambda is holomorphic on U (Morera/Fubini, differentiation under the integral); real-analytic parameter dependence follows by restriction
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8
REVIEWER: sol-review-P-j
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external; adds content to I:bpI:p7:x-param (only int_0^1 Phi(q,t mu) dt) and does not restate bpP:p7:e-hol (not an alias): carrier is a torus-parameter integral of a jointly continuous function; related nodes I:bpI:p7:x-param, I:bpI:p7:x-hol

NODE: bpP:p8:e-diff
KIND: external
TITLE: Differentiation under the integral:
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#bpP:p8:e-diff@L27-L27
PROOF_SOURCE: -
CONTRACT_ID: bpP:p8:e-diff
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: phi is C^k in w' with derivatives jointly continuous on [0,2pi]^n x U; 2pi-periodic continuous functions for the translation clause
SOURCE_QUANTIFIERS: k, U, phi, multi-index alpha with ¦alpha¦<=k
SOURCE_CONCLUSION: d^alpha <phi> = <d^alpha phi> for ¦alpha¦<=k; translation invariance of the integral of a 2pi-periodic continuous function; Fubini on products of intervals
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8+sol-review-P-j
REVIEWER: sol-delta-P-j
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external (Fubini on products of intervals; translation invariance of the period integral)

NODE: bpP:p8:e-taylor
KIND: external
TITLE: bpP:p8:e-taylor
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#bpP:p8:e-taylor@L28-L28
PROOF_SOURCE: -
CONTRACT_ID: bpP:p8:e-taylor
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: f real analytic near a point
SOURCE_QUANTIFIERS: f, point, order N
SOURCE_CONCLUSION: Taylor polynomial of order N has remainder O(¦x¦^(N+1)) locally uniformly; Taylor coefficients are the iterated derivatives; composition of an analytic function with a real-analytic map is real analytic
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8
REVIEWER: sol-review-P-j
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p8:e-weyl
KIND: external
TITLE: First fundamental theorem for $O(2)$
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#bpP:p8:e-weyl@L29-L29
PROOF_SOURCE: -
CONTRACT_ID: bpP:p8:e-weyl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: polynomial in vectors u_1,...,u_r in R^2 invariant under the diagonal action of O(2)
SOURCE_QUANTIFIERS: r, polynomial
SOURCE_CONCLUSION: the polynomial is a polynomial in the dot products u_i.u_j (first fundamental theorem for O(2))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8
REVIEWER: sol-review-P-j
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p8:e-poch
KIND: external
TITLE: bpP:p8:e-poch
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#bpP:p8:e-poch@L30-L30
PROOF_SOURCE: -
CONTRACT_ID: bpP:p8:e-poch
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: s real, p>=0, ¦z¦<1
SOURCE_QUANTIFIERS: s, p, z
SOURCE_CONCLUSION: Pochhammer (s)_p=s(s+1)...(s+p-1), (s)_{p+1}=(s)_p (s+p); (1-z)^{-s}=sum_p (s)_p/p! z^p for ¦z¦<1; (s)_p/p!=O(p^(s-1))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8
REVIEWER: sol-review-P-j
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p8:conv#data
KIND: definition
TITLE: Conventions and secular polydisc data of Part 8 (chart, averages, dictionary, N(rho))
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#bpP:p8:conv#data@L17-L22
PROOF_SOURCE: -
CONTRACT_ID: bpP:p8:conv#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n>=1; G,m0>0, kappa=G m0; m in (0,inf)^n; chart Psi=Psi^(n) of Theorem product-chart with hat f_fix=f_fix o Psi, hat f_mov=f_mov o Psi; axes 0<a_1*<...<a_n* (increasing); angles of period 2pi
SOURCE_QUANTIFIERS: n,G,m0,m,a*; then rho>0; then points (xi,Lambda,eta); for continuous phi on {(lambda,w')}
SOURCE_CONCLUSION: defines w=(lambda,xi,Lambda,eta), u_i=(xi_i,eta_i), Gamma_i=¦u_i¦^2/2, a_i=Lambda_i^2/(m_i^2 kappa), the average <phi>(w')=(2pi)^-n int phi dlambda, S_fix=<hat f_fix>, S_mov=<hat f_mov>, the dictionary to secularAverage (frozen p=eta, q=xi, I=Lambda, R_j=Gamma_j), Lambda_i*=m_i sqrt(kappa a_i*), N(rho), N_R(rho)=N(rho) cap R^(3n)
CONSTANT_SCOPE: kappa=G m0; a* and rho are fixed positive data; axes in increasing (Lean) order
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p7:product-chart, bpP:p7:product-def, bpP:p7:sec-product#data, bpP:p6:split, bpP:p0:blocks#assemble, bpP:p0:secavg#secularAverage
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p7:product-chart | blueprint-P/parts/p8-secular-form.tex#bpP:p8:conv#data@L17-L17 | chart Psi^(n) and hat f_fix, hat f_mov
EDGE: bpP:p7:product-def | blueprint-P/parts/p8-secular-form.tex#bpP:p8:conv#data@L17-L17 | Psi^(n), O_n
EDGE: bpP:p7:sec-product#data | blueprint-P/parts/p8-secular-form.tex#bpP:p8:conv#data@L17-L17 | coordinates w and data n, G, m0, m
EDGE: bpP:p6:split | blueprint-P/parts/p8-secular-form.tex#bpP:p8:conv#data@L17-L17 | f_fix, f_mov
EDGE: bpP:p0:blocks#assemble | blueprint-P/parts/p8-secular-form.tex#bpP:p8:conv#data@L19-L19 | assemble(I,phi,p,q)=((phi,q),(I,p)) in the dictionary
EDGE: bpP:p0:secavg#secularAverage | blueprint-P/parts/p8-secular-form.tex#bpP:p8:conv#data@L19-L19 | dictionary to the frozen secularAverage
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8
REVIEWER: sol-review-P-j
LEAN_STATUS: PROVED
LEAN_REF: Data, axes, action, axis, actionDomain, nu, secular, slowSecular, slowDom, cell, avg, rho, polydisc, inclusion, realDisc, perturbation (KAM/Planetary/SecularForm/Basic.lean)
LEAN_NOTE: audit S8-B PASS WITH NOTES; definitions only
NOTE: created from p8:prose-L17-L19 and p8:prose-L21-L22 (SPEC section data; N(rho), Lambda*, averages); consumers: nearly every node of Part 8 and Part 9

NODE: bpP:p8:rho
KIND: definition
TITLE: Secular polydisc constants
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#bpP:p8:rho@L33-L35
PROOF_SOURCE: -
CONTRACT_ID: bpP:p8:rho
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpP:p8:conv#data (n>=1; G,m0>0, kappa=G m0; m in (0,inf)^n; chart Psi=Psi^(n) with hat f_fix, hat f_mov; axes a*; N(rho))
SOURCE_QUANTIFIERS: data of conv#data; then rho_0 explicit; rho_* in (0,rho_0) fixed by bpP:p8:perturbation-analytic
SOURCE_CONCLUSION: defines rho_0=min_i min{Lambda_i*/2, sqrt(Lambda_i*)/16}, so that N(rho), rho<rho_0, lies in the domain of Prop holomorphic; rho_* is named as the constant of the proposition
CONSTANT_SCOPE: rho_0 depends only on Lambda* (hence on m,kappa,a*); rho_* depends only on (m,kappa,a*)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p8:conv#data, bpP:p7:holomorphic
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p8:conv#data | blueprint-P/parts/p8-secular-form.tex#bpP:p8:rho@L34-L34 | Lambda_i*, N(rho) and the data n, m, kappa, a*
EDGE: bpP:p7:holomorphic | blueprint-P/parts/p8-secular-form.tex#bpP:p8:rho@L34-L34 | the holomorphic chart domain in which N(rho) is asserted to lie
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8+sol-review-P-j
REVIEWER: sol-delta-P-j
LEAN_STATUS: PROVED
LEAN_REF: rho (KAM/Planetary/SecularForm/Basic.lean)
LEAN_NOTE: audit S8-B PASS WITH NOTES (definition PASS)
NOTE: rho_* is only named here (its existence is the content of bpP:p8:perturbation-analytic); no edge to that proposition (would be a cycle). The statement that N(rho), rho<rho_0, lies in the domain of Prop holomorphic is consumed at stepP:p8:pa-unif, which cites the proposition

NODE: bpP:p8:perturbation-analytic
KIND: proposition
TITLE: Analytic perturbation near the circular torus
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#bpP:p8:perturbation-analytic@L39-L46
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#bpP:p8:perturbation-analytic@L47-L52
CONTRACT_ID: bpP:p8:perturbation-analytic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpP:p8:conv#data (n>=1; G,m0>0, kappa=G m0; m in (0,inf)^n; chart Psi=Psi^(n) with hat f_fix, hat f_mov; axes a*; N(rho)); rho_0 of bpP:p8:rho; Psi of Prop holomorphic; s_ij=sum_c (q^(i)_c-q^(j)_c)^2 (complex bilinear square)
SOURCE_QUANTIFIERS: (m,kappa,a*); then rho_* in (0,rho_0); then real lambda, w' in N(rho_*), i<j
SOURCE_CONCLUSION: exists rho_* in (0,rho_0) depending only on (m,kappa,a*) such that: (a) Re s_ij>=(a_j*-a_i*)^2/2, real points ¦q^(i)-q^(j)¦>=(a_j*-a_i*)/sqrt2, Psi(lambda,w') in W and N_R(rho_*) x R^n subset Psi^-1(W); (b) hat f_fix=-G sum m_i m_j s_ij^(-1/2) holomorphic in w' for each real lambda, jointly continuous, 2pi-periodic, real at real points, likewise hat f_mov=hat f_fix+sum_c(sum_i p^(i)_c)^2/(2 m0) (bilinear square); (c) S_fix, S_mov holomorphic on N(rho_*), real at real points, real analytic on N_R(rho_*), d^alpha S=<d^alpha hat f>
CONSTANT_SCOPE: rho_* depends only on (m,kappa,a*), not on lambda or w'
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p8:pa-circ, stepP:p8:pa-unif, stepP:p8:pa-hol, stepP:p8:pa-avg, bpP:p8:conv#data, bpP:p8:rho, bpP:p7:holomorphic, bpP:p6:domain
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p8:pa-circ | blueprint-P/parts/p8-secular-form.tex#bpP:p8:perturbation-analytic@L48-L48 | proof step Value at the circular torus
EDGE: stepP:p8:pa-unif | blueprint-P/parts/p8-secular-form.tex#bpP:p8:perturbation-analytic@L49-L49 | proof step Uniformity
EDGE: stepP:p8:pa-hol | blueprint-P/parts/p8-secular-form.tex#bpP:p8:perturbation-analytic@L50-L50 | proof step Holomorphy
EDGE: stepP:p8:pa-avg | blueprint-P/parts/p8-secular-form.tex#bpP:p8:perturbation-analytic@L51-L51 | proof step The average
EDGE: bpP:p8:conv#data | blueprint-P/parts/p8-secular-form.tex#bpP:p8:perturbation-analytic@L40-L40 | data, Psi, hat f, a*, N(rho_*), averages
EDGE: bpP:p8:rho | blueprint-P/parts/p8-secular-form.tex#bpP:p8:perturbation-analytic@L40-L40 | rho_0 in the range of rho_*
EDGE: bpP:p7:holomorphic | blueprint-P/parts/p8-secular-form.tex#bpP:p8:perturbation-analytic@L40-L40 | q=Psi of Prop holomorphic in the definition of s_ij
EDGE: bpP:p6:domain | blueprint-P/parts/p8-secular-form.tex#bpP:p8:perturbation-analytic@L42-L42 | W of Lemma domain
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8
REVIEWER: sol-review-P-j
LEAN_STATUS: PROVED
LEAN_REF: perturbation_analytic_full (KAM/Planetary/SecularForm/AnalyticNodes.lean)
LEAN_NOTE: audit GAP-P8b round 3 PASS WITH NOTES
NOTE: -

NODE: stepP:p8:pa-circ
KIND: step
TITLE: Value at the circular torus
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:pa-circ@L48-L48
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:pa-circ@L48-L48
CONTRACT_ID: stepP:p8:pa-circ
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: w'*=(0,Lambda*,0); Theorem poincare(f): q^(i)=a_i*(cos lambda_i, sin lambda_i)
SOURCE_QUANTIFIERS: real lambda in R^n; i<j
SOURCE_CONCLUSION: s_ij=a_i*^2+a_j*^2-2 a_i* a_j* cos(lambda_i-lambda_j)>=(a_j*-a_i*)^2 at the circular torus
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p7:poincare, bpP:p8:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p7:poincare | blueprint-P/parts/p8-secular-form.tex#stepP:p8:pa-circ@L48-L48 | (f): circular values of q
EDGE: bpP:p8:conv#data | blueprint-P/parts/p8-secular-form.tex#stepP:p8:pa-circ@L48-L48 | a_i*, Lambda*
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8
REVIEWER: sol-review-P-j
LEAN_STATUS: PROVED
LEAN_REF: planetC_center, re_separationC_center (KAM/Planetary/SecularForm/AnalyticGeometry.lean)
LEAN_NOTE: audit S8-A PASS WITH NOTES; named pa-circ
NOTE: -

NODE: stepP:p8:pa-unif
KIND: step
TITLE: Uniformity
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:pa-unif@L49-L49
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:pa-unif@L49-L49
CONTRACT_ID: stepP:p8:pa-unif
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: s_ij holomorphic in w' on N(rho_0) and continuous 2pi-periodic in lambda; Step pa-circ
SOURCE_QUANTIFIERS: lambda in R^n; w' in N(rho_0/2) closure (compact)
SOURCE_CONCLUSION: exists rho_*<rho_0/2 depending only on (m,kappa,a*) with Re s_ij>=(a_j*-a_i*)^2/2 on [0,2pi]^n x N(rho_*), i.e. (a); at real points ¦q^(i)-q^(j)¦^2=s_ij and NoColl holds (¦q^(i)¦>0)
CONSTANT_SCOPE: rho_* depends only on (m,kappa,a*) (through Lambda* and Psi)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p7:holomorphic, stepP:p8:pa-circ, bpP:p7:o-facts, bpP:p7:poincare, bpP:p8:rho, bpP:p6:domain, bpP:p8:conv#data, bpP:p12:f-unif
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p7:holomorphic | blueprint-P/parts/p8-secular-form.tex#stepP:p8:pa-unif@L49-L49 | s_ij holomorphic on N(rho_0), Psi real at real points
EDGE: stepP:p8:pa-circ | blueprint-P/parts/p8-secular-form.tex#stepP:p8:pa-unif@L49-L49 | value at the circular torus gives the lower bound at w'*
EDGE: bpP:p7:o-facts | blueprint-P/parts/p8-secular-form.tex#stepP:p8:pa-unif@L49-L49 | ¦q^(i)¦>0 on O_n
EDGE: bpP:p7:poincare | blueprint-P/parts/p8-secular-form.tex#stepP:p8:pa-unif@L49-L49 | (d): Psi(O) in K, so q^(i)!=0
EDGE: bpP:p8:rho | blueprint-P/parts/p8-secular-form.tex#stepP:p8:pa-unif@L49-L49 | rho_0 and the polydisc N(rho_0/2)
EDGE: bpP:p6:domain | blueprint-P/parts/p8-secular-form.tex#stepP:p8:pa-unif@L49-L49 | NoColl and W (a: Psi in W)
EDGE: bpP:p8:conv#data | blueprint-P/parts/p8-secular-form.tex#stepP:p8:pa-unif@L49-L49 | N(rho), R^n torus domain
EDGE: bpP:p12:f-unif | blueprint-P/parts/p8-secular-form.tex#stepP:p8:pa-unif@L49-L49 | Heine-Cantor on the compact angle cell times the closed complex polydisc supplies uniform continuity and one collision-free radius rho_* for all real angles and pairs
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8
REVIEWER: sol-delta-P-bf
LEAN_STATUS: PROVED
LEAN_REF: perturbation_unif (KAM/Planetary/SecularForm/AnalyticNodes.lean)
LEAN_NOTE: audit GAP-P8b round 3 PASS WITH NOTES
NOTE: -

NODE: stepP:p8:pa-hol
KIND: step
TITLE: Holomorphy of $\hat f$
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:pa-hol@L50-L50
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:pa-hol@L50-L50
CONTRACT_ID: stepP:p8:pa-hol
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Re s_ij>=(a_j*-a_i*)^2/2 on N(rho_*) (Step pa-unif); principal s^(-1/2) holomorphic on Re s>0; Psi holomorphic
SOURCE_QUANTIFIERS: real lambda; w' in N(rho_*); i<j
SOURCE_CONCLUSION: (b): hat f_fix=-G sum m_i m_j s_ij^(-1/2) and hat f_mov are holomorphic in w', jointly continuous, 2pi-periodic, real at real points, equal to f_fix o Psi resp. f_mov o Psi
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: I:bpI:p7:x-hol, stepP:p8:pa-unif, bpP:p6:split, bpP:p7:holomorphic, bpP:p8:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: I:bpI:p7:x-hol | blueprint-P/parts/p8-secular-form.tex#stepP:p8:pa-hol@L50-L50 | principal s^(-1/2) holomorphic on Re s>0 and composition
EDGE: stepP:p8:pa-unif | blueprint-P/parts/p8-secular-form.tex#stepP:p8:pa-hol@L50-L50 | Re s_ij>0 on N(rho_*)
EDGE: bpP:p6:split | blueprint-P/parts/p8-secular-form.tex#stepP:p8:pa-hol@L50-L50 | formula equals f_fix o Psi; f_mov-f_fix=¦P¦^2/(2 m0)
EDGE: bpP:p7:holomorphic | blueprint-P/parts/p8-secular-form.tex#stepP:p8:pa-hol@L50-L50 | p^(i) holomorphic, Psi real at real points
EDGE: bpP:p8:conv#data | blueprint-P/parts/p8-secular-form.tex#stepP:p8:pa-hol@L50-L50 | hat f_fix, hat f_mov, and N(rho_*)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8+sol-review-P-j
REVIEWER: sol-delta-P-j
LEAN_STATUS: PROVED
LEAN_REF: perturbation_hol (KAM/Planetary/SecularForm/AnalyticNodes.lean)
LEAN_NOTE: audit GAP-P8b round 3 PASS WITH NOTES
NOTE: retargeted from bpP:p7:e-hol (excluded as alias in P-p7) to I:bpI:p7:x-hol; the Weierstrass part (I:bpI:p7:x-weier) is not used

NODE: stepP:p8:pa-avg
KIND: step
TITLE: The average
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:pa-avg@L51-L51
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:pa-avg@L51-L51
CONTRACT_ID: stepP:p8:pa-avg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: hat f holomorphic in w' on N(rho_*), jointly continuous and 2pi-periodic (Step pa-hol)
SOURCE_QUANTIFIERS: w' in N(rho_*)
SOURCE_CONCLUSION: (c): S holomorphic on N(rho_*), real at real points, real analytic on N_R(rho_*), d^alpha S=<d^alpha hat f>
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p8:pa-hol, bpP:p8:e-param, bpP:p8:e-diff, K:bp:p1:cauchy-open, K:bp:p1:holomorphic-analytic, bpP:p8:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p8:pa-hol | blueprint-P/parts/p8-secular-form.tex#stepP:p8:pa-avg@L51-L51 | f hat holomorphic, continuous, periodic
EDGE: bpP:p8:e-param | blueprint-P/parts/p8-secular-form.tex#stepP:p8:pa-avg@L51-L51 | S holomorphic
EDGE: bpP:p8:e-diff | blueprint-P/parts/p8-secular-form.tex#stepP:p8:pa-avg@L51-L51 | derivative formula
EDGE: K:bp:p1:cauchy-open | blueprint-P/parts/p8-secular-form.tex#stepP:p8:pa-avg@L51-L51 | Cauchy formula: derivatives jointly continuous, uniformly on the compact torus
EDGE: K:bp:p1:holomorphic-analytic | blueprint-P/parts/p8-secular-form.tex#stepP:p8:pa-avg@L51-L51 | holomorphic implies real analytic on the real part (restriction)
EDGE: bpP:p8:conv#data | blueprint-P/parts/p8-secular-form.tex#stepP:p8:pa-avg@L51-L51 | definition of S as the average
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8
REVIEWER: sol-review-P-j
LEAN_STATUS: PROVED
LEAN_REF: perturbation_avg_node (KAM/Planetary/SecularForm/AnalyticNodes.lean)
LEAN_NOTE: audit GAP-P8b round 3 PASS WITH NOTES
NOTE: -

NODE: bpP:p8:symmetries
KIND: proposition
TITLE: Symmetries of the chart
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#bpP:p8:symmetries@L58-L66
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#bpP:p8:symmetries@L67-L73
CONTRACT_ID: bpP:p8:symmetries
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpP:p8:conv#data (n>=1; G,m0>0, kappa=G m0; m in (0,inf)^n; chart Psi=Psi^(n) with hat f_fix, hat f_mov; axes a*; N(rho)); w in O_n, Psi(w)=(q,p) with blocks q^(i), p^(i); R_theta, sigma=diag(1,-1), 1=(1,...,1)
SOURCE_QUANTIFIERS: n,m,kappa; w in O_n; theta in R
SOURCE_CONCLUSION: (S1) Psi(lambda+pi 1,-xi,Lambda,-eta)=(-q,-p); (S2) Psi(lambda+theta 1,R_theta(xi,eta),Lambda)=(R_theta q^(i),R_theta p^(i)); (S3) Psi(-lambda,xi,Lambda,-eta)=(sigma q^(i),-sigma p^(i)); O_n invariant; f_fix,f_mov satisfy f(-q,-p)=f(q,p)=f(Rq,±Rp), R in O(2) blockwise
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p8:sy-1, stepP:p8:sy-2, stepP:p8:sy-3, stepP:p8:sy-f, bpP:p6:split, bpP:p7:product-def, bpP:p8:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p8:sy-1 | blueprint-P/parts/p8-secular-form.tex#bpP:p8:symmetries@L69-L69 | proof step (S1)
EDGE: stepP:p8:sy-2 | blueprint-P/parts/p8-secular-form.tex#bpP:p8:symmetries@L70-L70 | proof step (S2)
EDGE: stepP:p8:sy-3 | blueprint-P/parts/p8-secular-form.tex#bpP:p8:symmetries@L71-L71 | proof step (S3)
EDGE: stepP:p8:sy-f | blueprint-P/parts/p8-secular-form.tex#bpP:p8:symmetries@L72-L72 | proof step Kepler functions
EDGE: bpP:p6:split | blueprint-P/parts/p8-secular-form.tex#bpP:p8:symmetries@L65-L65 | f_fix, f_mov of Lemma split
EDGE: bpP:p7:product-def | blueprint-P/parts/p8-secular-form.tex#bpP:p8:symmetries@L59-L59 | Psi^(n), O_n
EDGE: bpP:p8:conv#data | blueprint-P/parts/p8-secular-form.tex#bpP:p8:symmetries@L59-L59 | the standing product chart Psi and physical data; R_theta and sigma are local notation from L56
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8+sol-review-P-j
REVIEWER: sol-delta-P-j
LEAN_STATUS: PROVED
LEAN_REF: symmetries, rotateSlow, rotatePhysical, rotateSlow_mem, perturbation_antipode, perturbation_rotate, perturbation_reflect (KAM/Planetary/SecularForm/Symmetry.lean)
LEAN_NOTE: audit S8-Y PASS WITH NOTES; chart identities (S1)-(S3) plus f invariances
NOTE: -

NODE: stepP:p8:sy-1
KIND: step
TITLE: (S1)
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:sy-1@L69-L69
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:sy-1@L69-L69
CONTRACT_ID: stepP:p8:sy-1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: one planet; Phi(F,v)=F-v_0 sin F+v_1 cos F; c=(cos F,sin F); q=a(kc-v+(v.c)v/(1+k)), p=m^2 kappa/(Lambda J) (J_0 c-(v.c)J_0 v/(1+k))
SOURCE_QUANTIFIERS: one planet; (lambda,v,Lambda)
SOURCE_CONCLUSION: Phi(F+pi,-v)=Phi(F,v)+pi so F(lambda+pi,-v)=F(lambda,v)+pi, c->-c, J,k unchanged, v->-v, hence (q,p)->(-q,-p): (S1)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p7:regular-kepler, bpP:p7:poincare-def
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p7:regular-kepler | blueprint-P/parts/p8-secular-form.tex#stepP:p8:sy-1@L69-L69 | (a): uniqueness of the solution F of the regular Kepler equation
EDGE: bpP:p7:poincare-def | blueprint-P/parts/p8-secular-form.tex#stepP:p8:sy-1@L69-L69 | formulas for q, p, v, k, J, c
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8
REVIEWER: sol-review-P-j
LEAN_STATUS: PROVED
LEAN_REF: poincare_antipode (KAM/Planetary/SecularForm/Symmetry.lean)
LEAN_NOTE: audit S8-Y PASS WITH NOTES; named sy-1
NOTE: -

NODE: stepP:p8:sy-2
KIND: step
TITLE: (S2)
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:sy-2@L70-L70
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:sy-2@L70-L70
CONTRACT_ID: stepP:p8:sy-2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: one planet; v positive multiple of (xi,eta) with Gamma,Lambda unchanged under rotation; R_theta J_0=J_0 R_theta
SOURCE_QUANTIFIERS: one planet; theta in R
SOURCE_CONCLUSION: v->R_theta v, Phi(F+theta,R_theta v)=Phi(F,v)+theta, so F(lambda+theta,R_theta v)=F+theta, c->R_theta c, J unchanged, (q,p)->(R_theta q,R_theta p): (S2)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p7:regular-kepler, bpP:p7:poincare-def
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p7:regular-kepler | blueprint-P/parts/p8-secular-form.tex#stepP:p8:sy-2@L70-L70 | (a): uniqueness of F
EDGE: bpP:p7:poincare-def | blueprint-P/parts/p8-secular-form.tex#stepP:p8:sy-2@L70-L70 | definition of v, q, p, J_0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8
REVIEWER: sol-review-P-j
LEAN_STATUS: PROVED
LEAN_REF: poincare_rotate (KAM/Planetary/SecularForm/Symmetry.lean)
LEAN_NOTE: audit S8-Y PASS WITH NOTES; named sy-2
NOTE: -

NODE: stepP:p8:sy-3
KIND: step
TITLE: (S3)
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:sy-3@L71-L71
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:sy-3@L71-L71
CONTRACT_ID: stepP:p8:sy-3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: one planet; bar v=sigma v (eta->-eta); J_0 sigma=-sigma J_0
SOURCE_QUANTIFIERS: one planet
SOURCE_CONCLUSION: Phi(-F,bar v)=-Phi(F,v), F(-lambda,bar v)=-F(lambda,v), c->sigma c, J unchanged, q->sigma q, p->-sigma p: (S3)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p7:regular-kepler, bpP:p7:poincare-def
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p7:regular-kepler | blueprint-P/parts/p8-secular-form.tex#stepP:p8:sy-3@L71-L71 | (a): uniqueness of F
EDGE: bpP:p7:poincare-def | blueprint-P/parts/p8-secular-form.tex#stepP:p8:sy-3@L71-L71 | definition of v, q, p, J_0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8
REVIEWER: sol-review-P-j
LEAN_STATUS: PROVED
LEAN_REF: poincare_reflect (KAM/Planetary/SecularForm/Symmetry.lean)
LEAN_NOTE: audit S8-Y PASS WITH NOTES; named sy-3
NOTE: -

NODE: stepP:p8:sy-f
KIND: step
TITLE: The Kepler functions
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:sy-f@L72-L72
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:sy-f@L72-L72
CONTRACT_ID: stepP:p8:sy-f
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: f_fix depends on ¦q_i-q_j¦; f_mov-f_fix=¦sum p_i¦^2/(2 m0)
SOURCE_QUANTIFIERS: common orthogonal linear map R in O(2), applied to every planet; independent overall signs on q and p
SOURCE_CONCLUSION: f_fix,f_mov invariant under (q,p)->(±Rq,±' Rp) for a common R in O(2) applied to all planets
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p6:split
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p6:split | blueprint-P/parts/p8-secular-form.tex#stepP:p8:sy-f@L72-L72 | f_fix depends on ¦q_i-q_j¦ and f_mov-f_fix=¦P¦^2/(2 m0)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8+sol-review-P-j
REVIEWER: sol-delta-P-j
LEAN_STATUS: PROVED
LEAN_REF: perturbation_map, perturbation_antipode, perturbation_rotate, perturbation_reflect (KAM/Planetary/SecularForm/Symmetry.lean)
LEAN_NOTE: audit S8-Y PASS WITH NOTES; named sy-f
NOTE: -

NODE: bpP:p8:evenness
KIND: corollary
TITLE: Evenness and invariance of the secular function
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#bpP:p8:evenness@L75-L80
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#bpP:p8:evenness@L81-L85
CONTRACT_ID: bpP:p8:evenness
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: S in {S_fix,S_mov} on N_R(rho_*) (rho_* of bpP:p8:perturbation-analytic)
SOURCE_QUANTIFIERS: n,m,kappa,a*; rho_*; (xi,Lambda,eta) in N_R(rho_*); theta
SOURCE_CONCLUSION: S(-xi,Lambda,-eta)=S(xi,Lambda,eta)=S(xi,Lambda,-eta)=S(-xi,Lambda,eta), S(R_theta(xi,eta),Lambda)=S(xi,Lambda,eta); Taylor expansion at (xi,eta)=0 has only even total degree, origin critical, degree-2d part O(2)-invariant polynomial in (u_1,...,u_n) with coefficients real-analytic in Lambda; degree-two part xi^T A(Lambda) xi+eta^T A(Lambda) eta, A=A^T
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p8:ev-inv, stepP:p8:ev-tay, stepP:p8:ev-quad, bpP:p8:perturbation-analytic, bpP:p8:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p8:ev-inv | blueprint-P/parts/p8-secular-form.tex#bpP:p8:evenness@L82-L82 | proof step Invariances
EDGE: stepP:p8:ev-tay | blueprint-P/parts/p8-secular-form.tex#bpP:p8:evenness@L83-L83 | proof step Taylor structure
EDGE: stepP:p8:ev-quad | blueprint-P/parts/p8-secular-form.tex#bpP:p8:evenness@L84-L84 | proof step Quadratic part
EDGE: bpP:p8:perturbation-analytic | blueprint-P/parts/p8-secular-form.tex#bpP:p8:evenness@L76-L76 | rho_*, S real analytic on N_R(rho_*)
EDGE: bpP:p8:conv#data | blueprint-P/parts/p8-secular-form.tex#bpP:p8:evenness@L76-L76 | S_fix, S_mov, N_R(rho), R_theta notation
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8
REVIEWER: sol-review-P-j
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: audit S8-Y PASS WITH NOTES: evenness proves the four invariances and evenness_taylor the vanishing of odd derivatives; criticality, O(2)-invariance of the degree-2d part and the A=A^T quadratic form are not exported; not marked proved
NOTE: suspected defect: S(R_theta(xi,eta),Lambda) needs R_theta(xi,eta) in N_R(rho_*), but N_R(rho) is the box ¦xi_i¦,¦eta_i¦<rho, which is not invariant under rotations by theta not in (pi/2)Z; the identity holds for small (xi,eta) (local invariance suffices for steps ev-tay, ev-quad)

NODE: stepP:p8:ev-inv
KIND: step
TITLE: Invariances
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:ev-inv@L82-L82
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:ev-inv@L82-L82
CONTRACT_ID: stepP:p8:ev-inv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Prop symmetries (S1)-(S3); hat f=f o Psi invariant; S=<hat f>
SOURCE_QUANTIFIERS: S in {S_fix,S_mov}
SOURCE_CONCLUSION: S is invariant under (xi,eta)->-(xi,eta), eta->-eta, xi->-xi, rotations R_theta; fourth equality from the first and second
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p8:symmetries, bpP:p8:e-diff, bpP:p8:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p8:symmetries | blueprint-P/parts/p8-secular-form.tex#stepP:p8:ev-inv@L82-L82 | (S1)-(S3) and invariance of f
EDGE: bpP:p8:e-diff | blueprint-P/parts/p8-secular-form.tex#stepP:p8:ev-inv@L82-L82 | translation invariance of the average of a periodic function
EDGE: bpP:p8:conv#data | blueprint-P/parts/p8-secular-form.tex#stepP:p8:ev-inv@L82-L82 | definition of S as the lambda-average
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8
REVIEWER: sol-review-P-j
LEAN_STATUS: PROVED
LEAN_REF: evenness, cell_integral_add, cell_integral_neg, perturbation_periodic (KAM/Planetary/SecularForm/Symmetry.lean)
LEAN_NOTE: audit S8-Y PASS WITH NOTES; named ev-inv
NOTE: -

NODE: stepP:p8:ev-tay
KIND: step
TITLE: Taylor structure
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:ev-tay@L83-L83
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:ev-tay@L83-L83
CONTRACT_ID: stepP:p8:ev-tay
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: S real analytic in (xi,eta); evenness under (xi,eta)->-(xi,eta); rotation invariance
SOURCE_QUANTIFIERS: S in {S_fix,S_mov}
SOURCE_CONCLUSION: odd-degree Taylor parts vanish; the degree-2d part of an O(2)-invariant analytic function is O(2)-invariant (O(2) linear, preserves homogeneity)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p8:perturbation-analytic, stepP:p8:ev-inv, bpP:p8:e-taylor, bpP:p8:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p8:perturbation-analytic | blueprint-P/parts/p8-secular-form.tex#stepP:p8:ev-tay@L83-L83 | (c): S real analytic in (xi,eta)
EDGE: stepP:p8:ev-inv | blueprint-P/parts/p8-secular-form.tex#stepP:p8:ev-tay@L83-L83 | evenness and invariance
EDGE: bpP:p8:e-taylor | blueprint-P/parts/p8-secular-form.tex#stepP:p8:ev-tay@L83-L83 | Taylor coefficients, expansion
EDGE: bpP:p8:conv#data | blueprint-P/parts/p8-secular-form.tex#stepP:p8:ev-tay@L83-L83 | the secular function S and its Taylor expansion in the slow coordinates
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8+sol-review-P-j
REVIEWER: sol-delta-P-j
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p8:ev-quad
KIND: step
TITLE: Quadratic part
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:ev-quad@L84-L84
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:ev-quad@L84-L84
CONTRACT_ID: stepP:p8:ev-quad
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: degree-two part xi^T A xi+2 xi^T B eta+eta^T C eta; evenness in eta alone; invariance under (xi,eta)->(-eta,xi)
SOURCE_QUANTIFIERS: degree-two part
SOURCE_CONCLUSION: B=0 and C=A
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p8:ev-inv, stepP:p8:ev-tay, bpP:p8:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p8:ev-inv | blueprint-P/parts/p8-secular-form.tex#stepP:p8:ev-quad@L84-L84 | evenness in eta alone and the rotation theta=pi/2
EDGE: stepP:p8:ev-tay | blueprint-P/parts/p8-secular-form.tex#stepP:p8:ev-quad@L84-L84 | degree-two part of the Taylor expansion
EDGE: bpP:p8:conv#data | blueprint-P/parts/p8-secular-form.tex#stepP:p8:ev-quad@L84-L84 | the slow coordinates xi, eta of the secular quadratic part
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8+sol-review-P-j
REVIEWER: sol-delta-P-j
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p8:lemma64
KIND: proposition
TITLE: Lemma 64, exactly
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#bpP:p8:lemma64@L89-L99
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#bpP:p8:lemma64@L100-L106
CONTRACT_ID: bpP:p8:lemma64
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpP:p8:conv#data (n>=1; G,m0>0, kappa=G m0; m in (0,inf)^n; chart Psi=Psi^(n) with hat f_fix, hat f_mov; axes a*; N(rho)); nu_i=kappa^2 m_i^3/Lambda_i^3
SOURCE_QUANTIFIERS: n,m,kappa; every w in O_n (no neighbourhood, no collision hypothesis)
SOURCE_CONCLUSION: (a) m_i nu_i d_{lambda_i} q^(i)=p^(i), d_{lambda_k} q^(i)=0 for k!=i; (b) (2pi)^-1 int p^(i) dlambda_i=0; (c) for j!=k (2pi)^-n int p^(j).p^(k) dlambda=0; (d) (2pi)^-n int ¦p^(i)¦^2 dlambda=m_i^2 kappa/a_i=m_i^4 kappa^2/Lambda_i^2; (e) (2pi)^-n int ¦sum p^(i)¦^2 dlambda=sum m_i^4 kappa^2/Lambda_i^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p8:l64-a, stepP:p8:l64-b, stepP:p8:l64-c, stepP:p8:l64-d, stepP:p8:l64-e, bpP:p7:product-def, bpP:p8:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p8:l64-a | blueprint-P/parts/p8-secular-form.tex#bpP:p8:lemma64@L101-L101 | proof step (a)
EDGE: stepP:p8:l64-b | blueprint-P/parts/p8-secular-form.tex#bpP:p8:lemma64@L102-L102 | proof step (b)
EDGE: stepP:p8:l64-c | blueprint-P/parts/p8-secular-form.tex#bpP:p8:lemma64@L103-L103 | proof step (c)
EDGE: stepP:p8:l64-d | blueprint-P/parts/p8-secular-form.tex#bpP:p8:lemma64@L104-L104 | proof step (d)
EDGE: stepP:p8:l64-e | blueprint-P/parts/p8-secular-form.tex#bpP:p8:lemma64@L105-L105 | proof step (e)
EDGE: bpP:p7:product-def | blueprint-P/parts/p8-secular-form.tex#bpP:p8:lemma64@L90-L90 | Psi^(n), O_n, q^(i), p^(i)
EDGE: bpP:p8:conv#data | blueprint-P/parts/p8-secular-form.tex#bpP:p8:lemma64@L90-L90 | data n, m, kappa and a_i=Lambda_i^2/(m_i^2 kappa)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8
REVIEWER: sol-review-P-j
LEAN_STATUS: PROVED
LEAN_REF: momentum, position, lemma64, lemma64_coordinates (KAM/Planetary/SecularForm/Momentum.lean)
LEAN_NOTE: audit S8-M PASS WITH NOTES; parts (a)-(e)
NOTE: -

NODE: stepP:p8:l64-a
KIND: step
TITLE: (a)
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-a@L101-L101
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-a@L101-L101
CONTRACT_ID: stepP:p8:l64-a
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: H_Kep=sum[¦p^(i)¦^2/(2 m_i)-kappa m_i/¦q^(i)¦] differentiable where each q^(i)!=0; H_Kep o Psi=h(Lambda); chart field identity; q^(i) depends only on (lambda_i,xi_i,Lambda_i,eta_i)
SOURCE_QUANTIFIERS: w in O_n
SOURCE_CONCLUSION: m_i nu_i d_{lambda_i} q^(i)=p^(i) and d_{lambda_k} q^(i)=0 (k!=i)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p6:kepler-part, bpP:p7:product-chart, bpP:p1:chart-field, bpP:p7:product-def, bpP:p8:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p6:kepler-part | blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-a@L101-L101 | decoupled Kepler Hamiltonian, no pair term
EDGE: bpP:p7:product-chart | blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-a@L101-L101 | (b): H_Kep o Psi=h(Lambda), form of X_h
EDGE: bpP:p1:chart-field | blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-a@L101-L101 | D Psi X_h=X_{H_Kep} o Psi (applied to the chart)
EDGE: bpP:p7:product-def | blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-a@L101-L101 | q^(i) depends only on block i
EDGE: bpP:p8:conv#data | blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-a@L101-L101 | nu_i and data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8
REVIEWER: sol-review-P-j
LEAN_STATUS: PROVED
LEAN_REF: lemma64, hasDerivAt_position (KAM/Planetary/SecularForm/Momentum.lean)
LEAN_NOTE: audit S8-M PASS WITH NOTES; named l64-a
NOTE: the edge to bpP:p6:hamilton-eqs is deleted: the step states that it does not use it (its hypotheses include the collision guard)

NODE: stepP:p8:l64-b
KIND: step
TITLE: (b)
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-b@L102-L102
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-b@L102-L102
CONTRACT_ID: stepP:p8:l64-b
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: q^(i) real analytic and 2pi-periodic in lambda_i; step (a); m_i nu_i>0
SOURCE_QUANTIFIERS: w in O_n
SOURCE_CONCLUSION: (2pi)^-1 int_0^{2pi} p^(i) dlambda_i=0 in R^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p7:poincare, stepP:p8:l64-a, K:bp:p1:ext-integral
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p7:poincare | blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-b@L102-L102 | (a): q^(i) real analytic and 2pi-periodic in lambda_i
EDGE: stepP:p8:l64-a | blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-b@L102-L102 | p^(i)=m_i nu_i d_{lambda_i} q^(i)
EDGE: K:bp:p1:ext-integral | blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-b@L102-L102 | the fundamental theorem of calculus integrates the C1 periodic position derivative to q(2 pi)-q(0)=0, giving zero mean momentum through p=m nu partial_lambda q
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8
REVIEWER: sol-delta-P-bf
LEAN_STATUS: PROVED
LEAN_REF: lemma64, avg_momentum (KAM/Planetary/SecularForm/Momentum.lean)
LEAN_NOTE: audit S8-M PASS WITH NOTES; named l64-b
NOTE: -

NODE: stepP:p8:l64-c
KIND: step
TITLE: (c)
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-c@L103-L103
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-c@L103-L103
CONTRACT_ID: stepP:p8:l64-c
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: p^(j).p^(k) continuous; p^(j) depends on lambda_j only, p^(k) on lambda_k only; step (b)
SOURCE_QUANTIFIERS: j!=k; w in O_n
SOURCE_CONCLUSION: (2pi)^-n int p^(j).p^(k) dlambda=0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p8:l64-b, bpP:p7:product-def, bpP:p7:poincare, bpP:p8:e-diff
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p8:l64-b | blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-c@L103-L103 | both single-period averages vanish
EDGE: bpP:p7:product-def | blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-c@L103-L103 | p^(j) depends only on lambda_j
EDGE: bpP:p7:poincare | blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-c@L103-L103 | (a): continuity
EDGE: bpP:p8:e-diff | blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-c@L103-L103 | Fubini on the product angle intervals to reduce or separate the torus average
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8+sol-review-P-j
REVIEWER: sol-delta-P-j
LEAN_STATUS: PROVED
LEAN_REF: lemma64, avg_cross (KAM/Planetary/SecularForm/Momentum.lean)
LEAN_NOTE: audit S8-M PASS WITH NOTES; named l64-c
NOTE: -

NODE: stepP:p8:l64-d
KIND: step
TITLE: (d)
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-d@L104-L104
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-d@L104-L104
CONTRACT_ID: stepP:p8:l64-d
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Gamma_i>0: p^(i)=Q_{m_i,kappa}(ell,g,Lambda,C), ell=lambda-g; circular case Gamma_i=0
SOURCE_QUANTIFIERS: w in O_n; planet i
SOURCE_CONCLUSION: (2pi)^-n int ¦p^(i)¦^2 dlambda=(2pi)^-1 int ¦p^(i)¦^2 dlambda_i=m_i^2 kappa/a_i=m_i^4 kappa^2/Lambda_i^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p7:po-del, bpP:p7:kepler, bpP:p8:conv#data, bpP:p7:product-def, bpP:p8:e-diff
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p7:po-del | blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-d@L104-L104 | p^(i)=Q(ell,g,Lambda,C), ell=lambda-g
EDGE: bpP:p7:kepler | blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-d@L104-L104 | (c): mean of ¦p¦^2 over one period equals m^2 kappa/a; circular case of the same item
EDGE: bpP:p8:conv#data | blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-d@L104-L104 | a_i=Lambda_i^2/(m_i^2 kappa)
EDGE: bpP:p7:product-def | blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-d@L104-L104 | planetwise independence reduces the full torus integral to the single lambda_i integral
EDGE: bpP:p8:e-diff | blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-d@L104-L104 | Fubini on the product angle intervals to reduce or separate the torus average
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8+sol-review-P-j
REVIEWER: sol-delta-P-j
LEAN_STATUS: PROVED
LEAN_REF: lemma64, avg_diag (KAM/Planetary/SecularForm/Momentum.lean)
LEAN_NOTE: audit S8-M PASS WITH NOTES; named l64-d
NOTE: -

NODE: stepP:p8:l64-e
KIND: step
TITLE: (e)
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-e@L105-L105
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-e@L105-L105
CONTRACT_ID: stepP:p8:l64-e
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: step (c) and (d)
SOURCE_QUANTIFIERS: w in O_n
SOURCE_CONCLUSION: (2pi)^-n int ¦sum p^(i)¦^2 dlambda=sum m_i^4 kappa^2/Lambda_i^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p8:l64-c, stepP:p8:l64-d
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p8:l64-c | blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-e@L105-L105 | cross terms vanish
EDGE: stepP:p8:l64-d | blueprint-P/parts/p8-secular-form.tex#stepP:p8:l64-e@L105-L105 | diagonal terms
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8
REVIEWER: sol-review-P-j
LEAN_STATUS: PROVED
LEAN_REF: lemma64, planeSq_sum_eq (KAM/Planetary/SecularForm/Momentum.lean)
LEAN_NOTE: audit S8-M PASS WITH NOTES; named l64-e
NOTE: -

NODE: bpP:p8:laplace-def
KIND: definition
TITLE: Laplace coefficients
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#bpP:p8:laplace-def@L110-L114
PROOF_SOURCE: -
CONTRACT_ID: bpP:p8:laplace-def
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: s>0, k in Z, alpha in [0,1)
SOURCE_QUANTIFIERS: s,k,alpha
SOURCE_CONCLUSION: defines b_s^(k)(alpha)=(2pi)^-1 int_0^{2pi} cos(kt)(1+alpha^2-2 alpha cos t)^(-s) dt so that (1+alpha^2-2 alpha cos t)^(-s)=sum_k b_s^(k)(alpha) e^{ikt}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8
REVIEWER: sol-review-P-j
LEAN_STATUS: PROVED
LEAN_REF: laplace_def (KAM/Planetary/SecularForm/LaplaceCoeff.lean); laplace_fourier (KAM/Planetary/SecularForm/Laplace.lean)
LEAN_NOTE: audit S8-L PASS WITH NOTES
NOTE: -

NODE: bpP:p8:laplace
KIND: lemma
TITLE: Series; local holomorphy
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#bpP:p8:laplace@L116-L120
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#bpP:p8:laplace@L121-L124
CONTRACT_ID: bpP:p8:laplace
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: s>0, k>=0, alpha in [0,1); b_s^(k) of Definition laplace-def
SOURCE_QUANTIFIERS: s>0; k>=0; alpha in [0,1)
SOURCE_CONCLUSION: b_s^(k)(alpha)=sum_q (s)_{q+k}(s)_q/((q+k)! q!) alpha^(2q+k), b_s^(-k)=b_s^(k); radius of convergence >=1, holomorphic on ¦alpha¦<1, real nonnegative on [0,1), strictly positive on (0,1), b_s^(0)(0)=1, b_s^(k)(0)=0 for k>0; real analytic for 0<alpha<1 and alpha->b_s^(k)(a_i/a_j) real analytic on {0<a_i<a_j}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p8:la-exp, stepP:p8:la-conv, bpP:p8:laplace-def, bpP:p8:e-taylor
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p8:la-exp | blueprint-P/parts/p8-secular-form.tex#bpP:p8:laplace@L122-L122 | proof step Expansion
EDGE: stepP:p8:la-conv | blueprint-P/parts/p8-secular-form.tex#bpP:p8:laplace@L123-L123 | proof step Convergence
EDGE: bpP:p8:laplace-def | blueprint-P/parts/p8-secular-form.tex#bpP:p8:laplace@L118-L118 | the coefficients b_s^(k)
EDGE: bpP:p8:e-taylor | blueprint-P/parts/p8-secular-form.tex#bpP:p8:laplace@L119-L119 | composition of analytic functions (alpha=a_i/a_j) is real analytic
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8
REVIEWER: sol-review-P-j
LEAN_STATUS: PROVED
LEAN_REF: laplace (KAM/Planetary/SecularForm/Laplace.lean); laplaceTerm, laplaceC, hasSum_laplaceTerm (KAM/Planetary/SecularForm/LaplaceCoeff.lean)
LEAN_NOTE: audit S8-L PASS WITH NOTES; all eight conjuncts of laplace
NOTE: -

NODE: stepP:p8:la-exp
KIND: step
TITLE: Expansion
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:la-exp@L122-L122
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:la-exp@L122-L122
CONTRACT_ID: stepP:p8:la-exp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 1+alpha^2-2 alpha cos t=(1-alpha e^{it})(1-alpha e^{-it}); binomial series
SOURCE_QUANTIFIERS: s>0; alpha<1; t real
SOURCE_CONCLUSION: the series sum_{p,q} (s)_p(s)_q/(p!q!) alpha^(p+q) e^{i(p-q)t} converges absolutely and uniformly in t; termwise integration against e^{-ikt}/(2pi) gives the series of Lemma laplace, evenness in k
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p8:e-poch, bpP:p8:laplace-def
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p8:e-poch | blueprint-P/parts/p8-secular-form.tex#stepP:p8:la-exp@L122-L122 | binomial series and the growth O(p^(s-1))
EDGE: bpP:p8:laplace-def | blueprint-P/parts/p8-secular-form.tex#stepP:p8:la-exp@L122-L122 | Fourier coefficient definition of b_s^(k)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8
REVIEWER: sol-review-P-j
LEAN_STATUS: PROVED
LEAN_REF: hasSum_kernel_complex (KAM/Planetary/SecularForm/LaplaceSeries.lean)
LEAN_NOTE: audit S8-L PASS WITH NOTES; named la-exp
NOTE: -

NODE: stepP:p8:la-conv
KIND: step
TITLE: Convergence
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:la-conv@L123-L123
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:la-conv@L123-L123
CONTRACT_ID: stepP:p8:la-conv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: coefficient of alpha^(2q+k) is O((q+k+1)^(s-1)(q+1)^(s-1)); all coefficients >=0
SOURCE_QUANTIFIERS: s>0; k>=0
SOURCE_CONCLUSION: radius of convergence >=1; b_s^(k)>0 on (0,1)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p8:e-poch, stepP:p8:la-exp, bpP:p8:laplace-def
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p8:e-poch | blueprint-P/parts/p8-secular-form.tex#stepP:p8:la-conv@L123-L123 | (s)_p/p!=O(p^(s-1)), positivity of the Pochhammer symbols
EDGE: stepP:p8:la-exp | blueprint-P/parts/p8-secular-form.tex#stepP:p8:la-conv@L123-L123 | the series coefficients
EDGE: bpP:p8:laplace-def | blueprint-P/parts/p8-secular-form.tex#stepP:p8:la-conv@L123-L123 | the Laplace coefficients b_s^(k) used in the statement or computation
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8+sol-review-P-j
REVIEWER: sol-delta-P-j
LEAN_STATUS: PROVED
LEAN_REF: hasSum_laplaceTerm (KAM/Planetary/SecularForm/LaplaceCoeff.lean); differentiableOn_laplaceC (KAM/Planetary/SecularForm/Laplace.lean)
LEAN_NOTE: audit S8-L PASS WITH NOTES; named la-conv
NOTE: -

NODE: bpP:p8:identities
KIND: lemma
TITLE: Two identities
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#bpP:p8:identities@L129-L135
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#bpP:p8:identities@L136-L140
CONTRACT_ID: bpP:p8:identities
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: alpha in [0,1); beta=b_{1/2}^(0), b=b_{1/2}^(1)
SOURCE_QUANTIFIERS: alpha in [0,1)
SOURCE_CONCLUSION: (I1) alpha beta''+2 beta'=b_{3/2}^(1); (I2) alpha^2 b''+2 alpha b'-2b=alpha b_{3/2}^(2)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p8:id-1, stepP:p8:id-2, bpP:p8:laplace, bpP:p8:laplace-def
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p8:id-1 | blueprint-P/parts/p8-secular-form.tex#bpP:p8:identities@L138-L138 | proof step (I1)
EDGE: stepP:p8:id-2 | blueprint-P/parts/p8-secular-form.tex#bpP:p8:identities@L139-L139 | proof step (I2)
EDGE: bpP:p8:laplace | blueprint-P/parts/p8-secular-form.tex#bpP:p8:identities@L137-L137 | series of Lemma laplace compared coefficientwise
EDGE: bpP:p8:laplace-def | blueprint-P/parts/p8-secular-form.tex#bpP:p8:identities@L130-L130 | the Laplace coefficients b_s^(k) used in the statement or computation
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8+sol-review-P-j
REVIEWER: sol-delta-P-j
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: audit S8-I PASS WITH NOTES: identities proved only for 0<alpha<1; the blueprint includes alpha=0 (design interior-domain specialization); not marked proved
NOTE: -

NODE: stepP:p8:id-1
KIND: step
TITLE: (I1)
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:id-1@L138-L138
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:id-1@L138-L138
CONTRACT_ID: stepP:p8:id-1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: beta=sum_q ((1/2)_q/q!)^2 alpha^(2q); (3/2)_p=(2p+1)(1/2)_p, (3/2)_{p-1}=2 (1/2)_p
SOURCE_QUANTIFIERS: alpha in [0,1); q>=1
SOURCE_CONCLUSION: coefficient of alpha^(2q-1) of alpha beta''+2 beta' is 2q(2q+1)((1/2)_q/q!)^2, equal to that of b_{3/2}^(1)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p8:laplace, bpP:p8:e-poch, bpP:p8:laplace-def
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p8:laplace | blueprint-P/parts/p8-secular-form.tex#stepP:p8:id-1@L138-L138 | series of b_{1/2}^(0) and b_{3/2}^(1)
EDGE: bpP:p8:e-poch | blueprint-P/parts/p8-secular-form.tex#stepP:p8:id-1@L138-L138 | the Pochhammer relations used in the coefficient comparison (introduced at L137)
EDGE: bpP:p8:laplace-def | blueprint-P/parts/p8-secular-form.tex#stepP:p8:id-1@L138-L138 | the Laplace coefficients b_s^(k) used in the statement or computation
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8+sol-review-P-j
REVIEWER: sol-delta-P-j
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p8:id-2
KIND: step
TITLE: (I2)
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:id-2@L139-L139
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:id-2@L139-L139
CONTRACT_ID: stepP:p8:id-2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: b=sum_q c_q alpha^(2q+1); (alpha^2 d^2+2 alpha d-2) alpha^m=(m+2)(m-1) alpha^m
SOURCE_QUANTIFIERS: alpha in [0,1); q>=0
SOURCE_CONCLUSION: coefficient of alpha^(2q+1) on both sides agree (q=0 both zero; q>=1 equal 2q(2q+3)c_q)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p8:laplace, bpP:p8:e-poch, bpP:p8:laplace-def
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p8:laplace | blueprint-P/parts/p8-secular-form.tex#stepP:p8:id-2@L139-L139 | series of b_{1/2}^(1) and b_{3/2}^(2)
EDGE: bpP:p8:e-poch | blueprint-P/parts/p8-secular-form.tex#stepP:p8:id-2@L139-L139 | the Pochhammer relations used in the coefficient comparison (introduced at L137)
EDGE: bpP:p8:laplace-def | blueprint-P/parts/p8-secular-form.tex#stepP:p8:id-2@L139-L139 | the Laplace coefficients b_s^(k) used in the statement or computation
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8+sol-review-P-j
REVIEWER: sol-delta-P-j
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p8:coeffs
KIND: definition
TITLE: Secular coefficients
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#bpP:p8:coeffs@L144-L150
PROOF_SOURCE: -
CONTRACT_ID: bpP:p8:coeffs
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a_1<...<a_n axes; alpha_ij=a_i/a_j<1 for i<j; G, m_i as in conv#data; Delta=diag(sqrt(Lambda_i))
SOURCE_QUANTIFIERS: n,G,m,a; Lambda
SOURCE_CONCLUSION: defines fraktur a_ij=G m_i m_j a_i b_{3/2}^(1)(alpha_ij)/(4 a_j^2)>0, fraktur b_ij=G m_i m_j a_i b_{3/2}^(2)(alpha_ij)/(4 a_j^2)>0 (i<j, symmetric extension), C_0(a)=-sum_{i<j} G m_i m_j a_j^-1 b_{1/2}^(0)(alpha_ij), hat q_jj=-sum_{k!=j} a_jk, hat q_jk=b_jk, Q_h=Delta^-1 hat q Delta^-1; all real analytic in Lambda on {a_1<...<a_n}, a=a(Lambda)
CONSTANT_SCOPE: none (functions of a, hence of Lambda)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p8:laplace-def, bpP:p8:laplace, bpP:p8:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p8:laplace-def | blueprint-P/parts/p8-secular-form.tex#bpP:p8:coeffs@L146-L146 | b_s^(k) in the definitions
EDGE: bpP:p8:laplace | blueprint-P/parts/p8-secular-form.tex#bpP:p8:coeffs@L149-L149 | real analyticity of the coefficients and positivity
EDGE: bpP:p8:conv#data | blueprint-P/parts/p8-secular-form.tex#bpP:p8:coeffs@L145-L145 | data n, G, m, axes and a(Lambda)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8
REVIEWER: sol-review-P-j
LEAN_STATUS: PROVED
LEAN_REF: pairA, pairB, constantTerm, qhat, coeffs, coeffs_hermitian, coeffs_analytic (KAM/Planetary/SecularForm/Coefficients.lean)
LEAN_NOTE: audit S8-C PASS WITH NOTES; analyticity stated in the axes a on increasing positive axes
NOTE: -

NODE: bpP:p8:quadratic-form
KIND: theorem
TITLE: Quadratic part of the secular function
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#bpP:p8:quadratic-form@L152-L158
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#bpP:p8:quadratic-form@L159-L171
CONTRACT_ID: bpP:p8:quadratic-form
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: situation of bpP:p8:perturbation-analytic; a* increasing; (xi,Lambda,eta) in N_R(rho_*) with a(Lambda) increasing there (rho_* shrunk if needed); for the last clause varrho in SO(n) with Q_h=varrho diag(sigma) varrho^T
SOURCE_QUANTIFIERS: data of conv#data and Definition coeffs; rho_*; then points; varrho
SOURCE_CONCLUSION: S_fix=C_0(a)+xi^T Q_h xi+eta^T Q_h eta+O(¦(xi,eta)¦^4), error real analytic and O(¦(xi,eta)¦^4) locally uniformly in Lambda; the matrix A of the evenness corollary is Q_h; in (tilde xi,tilde eta)=varrho^T(xi,eta) the quadratic part is sum_j sigma_j(tilde xi_j^2+tilde eta_j^2)=sum_j 2 sigma_j tilde Gamma_j, i.e. Omega_j=2 sigma_j in the frozen sense
CONSTANT_SCOPE: rho_* depends only on (m,kappa,a*) (possibly shrunk for a(Lambda) increasing); the O-constant is locally uniform in Lambda
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p8:qf-pair, stepP:p8:qf-scale, stepP:p8:qf-c0, stepP:p8:qf-diag, stepP:p8:qf-cross, stepP:p8:qf-assembly, stepP:p8:qf-diag2, bpP:p8:perturbation-analytic, bpP:p8:evenness, bpP:p8:coeffs, bpP:p8:conv#data, bpP:p0:birkhoff#HasSecularBirkhoffForm
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p8:qf-pair | blueprint-P/parts/p8-secular-form.tex#bpP:p8:quadratic-form@L160-L160 | proof step Pair decomposition
EDGE: stepP:p8:qf-scale | blueprint-P/parts/p8-secular-form.tex#bpP:p8:quadratic-form@L161-L161 | proof step Scaling
EDGE: stepP:p8:qf-c0 | blueprint-P/parts/p8-secular-form.tex#bpP:p8:quadratic-form@L162-L162 | proof step C_0
EDGE: stepP:p8:qf-diag | blueprint-P/parts/p8-secular-form.tex#bpP:p8:quadratic-form@L163-L163 | proof step Diagonal coefficients
EDGE: stepP:p8:qf-cross | blueprint-P/parts/p8-secular-form.tex#bpP:p8:quadratic-form@L166-L166 | proof step Cross coefficient
EDGE: stepP:p8:qf-assembly | blueprint-P/parts/p8-secular-form.tex#bpP:p8:quadratic-form@L169-L169 | proof step Assembly
EDGE: stepP:p8:qf-diag2 | blueprint-P/parts/p8-secular-form.tex#bpP:p8:quadratic-form@L170-L170 | proof step Diagonalisation
EDGE: bpP:p8:perturbation-analytic | blueprint-P/parts/p8-secular-form.tex#bpP:p8:quadratic-form@L153-L153 | situation, rho_*, S_fix analytic on N_R(rho_*)
EDGE: bpP:p8:evenness | blueprint-P/parts/p8-secular-form.tex#bpP:p8:quadratic-form@L155-L155 | matrix A of the evenness corollary
EDGE: bpP:p8:coeffs | blueprint-P/parts/p8-secular-form.tex#bpP:p8:quadratic-form@L154-L154 | C_0, Q_h
EDGE: bpP:p8:conv#data | blueprint-P/parts/p8-secular-form.tex#bpP:p8:quadratic-form@L154-L154 | S_fix, N_R, data
EDGE: bpP:p0:birkhoff#HasSecularBirkhoffForm | blueprint-P/parts/p8-secular-form.tex#bpP:p8:quadratic-form@L155-L155 | frozen sense of Omega_j (R_j=Gamma_j)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8
REVIEWER: sol-review-P-j
LEAN_STATUS: PROVED
LEAN_REF: quadratic_form (KAM/Planetary/SecularForm/Quadratic.lean); qfDiagSymplectic, qfDiagSumSq, qfDiagIdentity (KAM/Planetary/SecularForm/Quadratic/Diag.lean)
LEAN_NOTE: audit S8-Q round 2 PASS WITH NOTES; signed quadratic_form plus Diag exports for the last clause
NOTE: edge to bpP:p8:factor-half deleted (remark: erratum and normalisation comparison, no proof consumes it; the factor 1/2 is proved here). The sourcegap at L157 (calculation only in [LR95], not pinned) is closed by the blueprint proof steps

NODE: stepP:p8:qf-pair
KIND: step
TITLE: Pair decomposition
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-pair@L160-L160
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-pair@L160-L160
CONTRACT_ID: stepP:p8:qf-pair
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: hat f_fix=sum_{i<j} V_ij, V_ij=-G m_i m_j/¦q^(i)-q^(j)¦ depends on (lambda_i,lambda_j) and (u_i,Lambda_i,u_j,Lambda_j) only
SOURCE_QUANTIFIERS: pairs i<j
SOURCE_CONCLUSION: S_fix=sum S_ij with S_ij=<V_ij> (average over lambda_i,lambda_j by Fubini); Cor evenness applies to each S_ij (n=2 function of (u_i,u_j)); degree-two part A_ij ¦u_i¦^2+A'_ij ¦u_j¦^2+B_ij u_i.u_j
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p8:evenness, bpP:p8:e-weyl, bpP:p8:perturbation-analytic, bpP:p8:conv#data, bpP:p7:product-def, bpP:p8:e-diff
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p8:evenness | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-pair@L160-L160 | evenness corollary applied to the n=2 function S_ij
EDGE: bpP:p8:e-weyl | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-pair@L160-L160 | quadratic O(2)-invariants of two vectors are spanned by the three dot products
EDGE: bpP:p8:perturbation-analytic | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-pair@L160-L160 | formula hat f_fix=-G sum m_i m_j s_ij^(-1/2) and analyticity
EDGE: bpP:p8:conv#data | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-pair@L160-L160 | S_fix and averages
EDGE: bpP:p7:product-def | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-pair@L160-L160 | each planet position depends only on its own fast angle and slow block
EDGE: bpP:p8:e-diff | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-pair@L160-L160 | Fubini on the product angle intervals to reduce or separate the torus average
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8+sol-review-P-j
REVIEWER: sol-delta-P-j
LEAN_STATUS: PROVED
LEAN_REF: secular_eq_sum_pair (KAM/Planetary/SecularForm/Quadratic/PairSplit.lean); secular_pair_eq, pairSlowSecular_swap (KAM/Planetary/SecularForm/Quadratic/PairIdentify.lean); hessian_pair_form, pair_second_derivative (KAM/Planetary/SecularForm/Quadratic/PairHessian.lean)
LEAN_NOTE: audit S8-Q round 2 PASS WITH NOTES
NOTE: -

NODE: stepP:p8:qf-scale
KIND: step
TITLE: Scaling
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-scale@L161-L161
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-scale@L161-L161
CONTRACT_ID: stepP:p8:qf-scale
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Phi(r_1,r_2)=(2pi)^-1 int (r_1^2+r_2^2-2 r_1 r_2 cos t)^(-1/2) dt
SOURCE_QUANTIFIERS: r_1,r_2>0, r_1!=r_2
SOURCE_CONCLUSION: Phi(r_1,r_2)=r_2^-1 b_{1/2}^(0)(r_1/r_2) for r_1<r_2, symmetric, real analytic on {r_1!=r_2}, homogeneous of degree -1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p8:laplace-def, bpP:p8:laplace
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p8:laplace-def | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-scale@L161-L161 | b_{1/2}^(0)
EDGE: bpP:p8:laplace | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-scale@L161-L161 | real analyticity of alpha->b_{1/2}^(0)(alpha)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8
REVIEWER: sol-review-P-j
LEAN_STATUS: PROVED
LEAN_REF: radialPhi_comm, radialPhi_smul, radialPhi_eq_laplace, analyticOnNhd_radialPhi (KAM/Planetary/SecularForm/DiagonalJet/Radial.lean)
LEAN_NOTE: audit S8-D PASS WITH NOTES (internal proof cut of quadratic_form, consumed by S8-Q audit 2 PASS WITH NOTES)
NOTE: -

NODE: stepP:p8:qf-c0
KIND: step
TITLE: $C_0$
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-c0@L162-L162
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-c0@L162-L162
CONTRACT_ID: stepP:p8:qf-c0
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u=0: both planets circular (Thm poincare(f)); S_ij(0)=<V_ij>
SOURCE_QUANTIFIERS: pairs i<j
SOURCE_CONCLUSION: S_ij(0)=-G m_i m_j Phi(a_i,a_j)=-G m_i m_j a_j^-1 b_{1/2}^(0)(alpha_ij)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p7:poincare, stepP:p8:qf-scale, stepP:p8:qf-pair, bpP:p8:conv#data, bpP:p8:laplace-def
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p7:poincare | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-c0@L162-L162 | (f): circular orbits at u=0
EDGE: stepP:p8:qf-scale | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-c0@L162-L162 | Phi and b_{1/2}^(0)
EDGE: stepP:p8:qf-pair | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-c0@L162-L162 | S_ij=<V_ij>
EDGE: bpP:p8:conv#data | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-c0@L162-L162 | u_i, the axes a_i=a_i(Lambda_i), and the circular value of the secular pair average
EDGE: bpP:p8:laplace-def | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-c0@L162-L162 | the Laplace coefficients b_s^(k) used in the statement or computation
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8+sol-review-P-j
REVIEWER: sol-delta-P-j
LEAN_STATUS: PROVED
LEAN_REF: pairSlowSecular_zero (KAM/Planetary/SecularForm/DiagonalJet/Pair.lean)
LEAN_NOTE: audit S8-D PASS WITH NOTES (internal proof cut of quadratic_form, consumed by S8-Q audit 2 PASS WITH NOTES)
NOTE: -

NODE: stepP:p8:qf-diag
KIND: step
TITLE: Diagonal coefficients
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-diag@L163-L165
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-diag@L163-L165
CONTRACT_ID: stepP:p8:qf-diag
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u_j=0 (j circular), u_i=(xi_i,eta_i); Prop kepler(b): ¦q^(i)¦=a_i(1-e cos u), d lambda_i=(1-e cos u)du; e^2=¦v_i¦^2=2Gamma_i/Lambda_i-Gamma_i^2/Lambda_i^2=:E; identity (I1)
SOURCE_QUANTIFIERS: i!=j
SOURCE_CONCLUSION: coefficient of ¦u_i¦^2 in S_ij at u_j=0 is -fraktur a_ij/Lambda_i, in both orderings i<j and i>j
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p7:kepler, bpP:p7:o-facts, I:bpI:p7:orbit-identities, bpP:p7:poincare, stepP:p8:qf-scale, stepP:p8:qf-pair, bpP:p8:identities, bpP:p8:e-taylor, bpP:p8:coeffs, bpP:p7:poincare-def, bpP:p8:conv#data, bpP:p8:laplace-def, bpP:p8:e-diff
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p7:kepler | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-diag@L163-L163 | (b): ¦q¦=a(1-e cos u), mean-anomaly relation
EDGE: bpP:p7:o-facts | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-diag@L163-L163 | e^2=¦v¦^2=E in terms of Gamma, Lambda
EDGE: I:bpI:p7:orbit-identities | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-diag@L163-L163 | d lambda=(1-e cos u)du, r=a(1-e cos u)
EDGE: bpP:p7:poincare | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-diag@L163-L163 | (f): circular planet j (u_j=0)
EDGE: stepP:p8:qf-scale | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-diag@L164-L164 | Phi(a_i(1-epsilon),a_j) and its radial derivatives in h
EDGE: stepP:p8:qf-pair | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-diag@L163-L163 | S_ij=<V_ij>
EDGE: bpP:p8:identities | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-diag@L165-L165 | identity (I1) evaluates the radial derivative expression
EDGE: bpP:p8:e-taylor | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-diag@L165-L165 | Taylor expansion of h and E=¦u¦^2/Lambda+O(¦u¦^4)
EDGE: bpP:p8:coeffs | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-diag@L165-L165 | identification with fraktur a_ij
EDGE: bpP:p7:poincare-def | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-diag@L165-L165 | v=(1-Gamma/(2 Lambda))^(1/2) Lambda^(-1/2) u
EDGE: bpP:p8:conv#data | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-diag@L163-L163 | u_i=(xi_i,eta_i), Gamma_i, a_i(Lambda_i), and the normalized angle averages
EDGE: bpP:p8:laplace-def | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-diag@L165-L165 | the Laplace coefficients b_s^(k) used in the statement or computation
EDGE: bpP:p8:e-diff | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-diag@L163-L163 | Fubini on the product angle intervals to reduce or separate the torus average
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8+sol-review-P-j
REVIEWER: sol-delta-P-j
LEAN_STATUS: PROVED
LEAN_REF: pairSlowSecular_diag_jet (KAM/Planetary/SecularForm/DiagonalJet.lean); iteratedDeriv_two_radialH_of_lt, iteratedDeriv_two_radialH_of_gt (KAM/Planetary/SecularForm/DiagonalJet/Radial.lean)
LEAN_NOTE: audit S8-D PASS WITH NOTES (internal proof cut of quadratic_form, consumed by S8-Q audit 2 PASS WITH NOTES)
NOTE: -

NODE: stepP:p8:qf-cross
KIND: step
TITLE: Cross coefficient
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-cross@L166-L168
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-cross@L166-L168
CONTRACT_ID: stepP:p8:qf-cross
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: i<j; B_ij=d_{xi_i}d_{xi_j}<V_ij> at 0; first-order orbit formulas in v with v=(1-Gamma/2Lambda)^(1/2)Lambda^(-1/2)u; B_k=r_j^-1 b_{1/2}^(k)(r_i/r_j) homogeneous of degree -1; identity (I2)
SOURCE_QUANTIFIERS: i<j
SOURCE_CONCLUSION: B_ij=2 fraktur b_ij/sqrt(Lambda_i Lambda_j) (partial_s partial_t <V_ij>=2 fraktur b_ij)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p8:e-diff, bpP:p7:regular-kepler, bpP:p7:poincare-def, bpP:p8:laplace-def, bpP:p8:identities, stepP:p8:qf-pair, bpP:p8:coeffs, bpP:p8:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p8:e-diff | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-cross@L166-L166 | differentiation under the average
EDGE: bpP:p7:regular-kepler | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-cross@L166-L166 | (a): d_v F=(sin F,-cos F) at v=0, F=lambda, J=1
EDGE: bpP:p7:poincare-def | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-cross@L166-L166 | v in terms of u; position formula q=a(kc-v+(v.c)v/(1+k))
EDGE: bpP:p8:laplace-def | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-cross@L166-L166 | Fourier expansion of U in Laplace coefficients B_k
EDGE: bpP:p8:identities | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-cross@L168-L168 | identity (I2) evaluates the mixed coefficient
EDGE: stepP:p8:qf-pair | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-cross@L166-L166 | V_ij, S_ij=<V_ij>
EDGE: bpP:p8:coeffs | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-cross@L168-L168 | identification with fraktur b_ij
EDGE: bpP:p8:conv#data | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-cross@L166-L166 | u_i, Gamma_i and the normalized averages in the slow chart coordinates
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8+sol-review-P-j
REVIEWER: sol-delta-P-j
LEAN_STATUS: PROVED
LEAN_REF: cross_hessian (KAM/Planetary/SecularForm/CrossJet.lean)
LEAN_NOTE: audit S8-X PASS WITH NOTES (internal proof cut of quadratic_form, consumed by S8-Q audit 2 PASS WITH NOTES)
NOTE: -

NODE: stepP:p8:qf-assembly
KIND: step
TITLE: Assembly
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-assembly@L169-L169
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-assembly@L169-L169
CONTRACT_ID: stepP:p8:qf-assembly
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: degree-two part of S_fix-C_0 as the sum of the diagonal and cross coefficients; remainder analytic with vanishing jet to order three
SOURCE_QUANTIFIERS: (xi,Lambda,eta) in N_R(rho_*)
SOURCE_CONCLUSION: quadratic part sum_{j,k}(Q_h)_jk(xi_j xi_k+eta_j eta_k), remainder O(¦(xi,eta)¦^4); rho_* shrunk so that a(Lambda) is increasing
CONSTANT_SCOPE: shrinking depends only on continuity of a(Lambda)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p8:qf-c0, stepP:p8:qf-diag, stepP:p8:qf-cross, stepP:p8:qf-pair, bpP:p8:evenness, bpP:p8:e-taylor, bpP:p8:coeffs, bpP:p8:perturbation-analytic, bpP:p8:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p8:qf-c0 | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-assembly@L169-L169 | the constant C_0 subtracted from S_fix
EDGE: stepP:p8:qf-diag | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-assembly@L169-L169 | diagonal coefficients
EDGE: stepP:p8:qf-cross | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-assembly@L169-L169 | cross coefficient
EDGE: stepP:p8:qf-pair | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-assembly@L169-L169 | sum over pairs
EDGE: bpP:p8:evenness | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-assembly@L169-L169 | vanishing jet up to order three
EDGE: bpP:p8:e-taylor | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-assembly@L169-L169 | O(¦(xi,eta)¦^4) from the vanishing jet of an analytic remainder
EDGE: bpP:p8:coeffs | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-assembly@L169-L169 | Q_h, C_0 definitions
EDGE: bpP:p8:perturbation-analytic | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-assembly@L169-L169 | analyticity on N_R(rho_*)
EDGE: bpP:p8:conv#data | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-assembly@L169-L169 | S_fix, u_i, and N_R(rho_*) with a=a(Lambda)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8+sol-review-P-j
REVIEWER: sol-delta-P-j
LEAN_STATUS: PROVED
LEAN_REF: quad_pair_sum (KAM/Planetary/SecularForm/Quadratic/Algebra.lean); iteratedDeriv_rayRemainder (KAM/Planetary/SecularForm/Quadratic/Jet.lean); exists_remainder_constants (KAM/Planetary/SecularForm/Quadratic/Constants.lean)
LEAN_NOTE: audit S8-Q round 2 PASS WITH NOTES
NOTE: -

NODE: stepP:p8:qf-diag2
KIND: step
TITLE: Diagonalisation
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-diag2@L170-L170
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-diag2@L170-L170
CONTRACT_ID: stepP:p8:qf-diag2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: varrho in SO(n) with Q_h=varrho diag(sigma) varrho^T; step Assembly
SOURCE_QUANTIFIERS: varrho; (xi,eta)
SOURCE_CONCLUSION: (xi,eta)->(varrho^T xi,varrho^T eta) is symplectic for d eta^ d xi, preserves sum(xi_j^2+eta_j^2); Gamma tilde_j=(tilde xi_j^2+tilde eta_j^2)/2, so quadratic part=sum 2 sigma_j tilde Gamma_j
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p8:qf-assembly, bpP:p8:coeffs, bpP:p0:hamsymp#symplecticForm, bpP:p8:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p8:qf-assembly | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-diag2@L170-L170 | quadratic part xi^T Q_h xi+eta^T Q_h eta
EDGE: bpP:p8:coeffs | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-diag2@L170-L170 | Q_h
EDGE: bpP:p0:hamsymp#symplecticForm | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-diag2@L170-L170 | symplectic for the frozen form
EDGE: bpP:p8:conv#data | blueprint-P/parts/p8-secular-form.tex#stepP:p8:qf-diag2@L170-L170 | the slow-coordinate order and Gamma_j=(xi_j^2+eta_j^2)/2
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8+sol-review-P-j
REVIEWER: sol-delta-P-j
LEAN_STATUS: PROVED
LEAN_REF: qfDiagSymplectic, qfDiagSumSq, qfDiagIdentity (KAM/Planetary/SecularForm/Quadratic/Diag.lean)
LEAN_NOTE: audit S8-Q round 2 PASS WITH NOTES; F1 resolved
NOTE: -

NODE: bpP:p8:identification
KIND: theorem
TITLE: Identification of $\langle H_{\rm mov}\rangle$ and $\langle H_{\rm fix}\rangle$
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#bpP:p8:identification@L182-L189
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#bpP:p8:identification@L190-L194
CONTRACT_ID: bpP:p8:identification
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpP:p8:conv#data (n>=1; G,m0>0, kappa=G m0; m in (0,inf)^n; chart Psi=Psi^(n) with hat f_fix, hat f_mov; axes a*; N(rho)); w'=(xi,Lambda,eta) with (lambda,xi,Lambda,eta) in O_n; delta(Lambda)=(2 m0)^-1 sum m_i^4 kappa^2/Lambda_i^2=(G/2) sum m_i^2/a_i
SOURCE_QUANTIFIERS: n,G,m0,m; w' with lambda in O_n-fibre
SOURCE_CONCLUSION: lambda->hat f_mov-hat f_fix=¦sum p^(i)¦^2/(2 m0) is continuous and its average is delta(Lambda); hat f_fix(.,w') integrable iff hat f_mov(.,w') is, then S_mov=S_fix+delta(Lambda), in particular on N_R(rho_*); <H_mov^Psi>=h+mu S_mov=h+mu S_fix+mu delta, <H_fix^Psi>=h+eps S_fix
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p8:id-diff, stepP:p8:id-avg, stepP:p8:id-int, bpP:p8:perturbation-analytic, bpP:p7:product-chart, bpP:p8:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p8:id-diff | blueprint-P/parts/p8-secular-form.tex#bpP:p8:identification@L191-L191 | proof step Difference
EDGE: stepP:p8:id-avg | blueprint-P/parts/p8-secular-form.tex#bpP:p8:identification@L192-L192 | proof step Average
EDGE: stepP:p8:id-int | blueprint-P/parts/p8-secular-form.tex#bpP:p8:identification@L193-L193 | proof step Integrability
EDGE: bpP:p8:perturbation-analytic | blueprint-P/parts/p8-secular-form.tex#bpP:p8:identification@L187-L187 | N_R(rho_*) where both are analytic
EDGE: bpP:p7:product-chart | blueprint-P/parts/p8-secular-form.tex#bpP:p8:identification@L187-L187 | (c): H_mov^Psi=h+mu f_mov o Psi, H_fix^Psi=h+eps f_fix o Psi
EDGE: bpP:p8:conv#data | blueprint-P/parts/p8-secular-form.tex#bpP:p8:identification@L183-L183 | data, averages, S_fix, S_mov
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8
REVIEWER: sol-review-P-j
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: audit S8-M PASS WITH NOTES: identification proves continuity, the average delta, the integrability iff and the guarded S_mov=S_fix+delta; the N_R(rho_*) specialization and the averaged-Hamiltonian clauses are not exported; not marked proved
NOTE: -

NODE: stepP:p8:id-diff
KIND: step
TITLE: Difference
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:id-diff@L191-L191
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:id-diff@L191-L191
CONTRACT_ID: stepP:p8:id-diff
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: f_mov-f_fix=¦P¦^2/(2 m0) identically (Lemma split); p^(i)(lambda_i) continuous
SOURCE_QUANTIFIERS: w' with lambda in O_n
SOURCE_CONCLUSION: hat f_mov-hat f_fix=¦sum p^(i)¦^2/(2 m0) is a polynomial in the continuous p^(i)(lambda_i), hence continuous
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p6:split, bpP:p7:poincare, bpP:p7:product-def, bpP:p8:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p6:split | blueprint-P/parts/p8-secular-form.tex#stepP:p8:id-diff@L191-L191 | f_mov-f_fix=¦P¦^2/(2 m0)
EDGE: bpP:p7:poincare | blueprint-P/parts/p8-secular-form.tex#stepP:p8:id-diff@L191-L191 | (a): p^(i) real analytic hence continuous
EDGE: bpP:p7:product-def | blueprint-P/parts/p8-secular-form.tex#stepP:p8:id-diff@L191-L191 | p^(i) depends on lambda_i only
EDGE: bpP:p8:conv#data | blueprint-P/parts/p8-secular-form.tex#stepP:p8:id-diff@L191-L191 | hat f_mov=f_mov o Psi and hat f_fix=f_fix o Psi
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8+sol-review-P-j
REVIEWER: sol-delta-P-j
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p8:id-avg
KIND: step
TITLE: Average
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:id-avg@L192-L192
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:id-avg@L192-L192
CONTRACT_ID: stepP:p8:id-avg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Prop lemma64(e); kappa/m0=G
SOURCE_QUANTIFIERS: w' as in the statement
SOURCE_CONCLUSION: (2pi)^-n int(hat f_mov-hat f_fix) dlambda=delta(Lambda), including the form (G/2) sum m_i^2/a_i
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p8:lemma64, stepP:p8:id-diff, bpP:p8:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p8:lemma64 | blueprint-P/parts/p8-secular-form.tex#stepP:p8:id-avg@L192-L192 | (e): average of ¦sum p^(i)¦^2
EDGE: stepP:p8:id-diff | blueprint-P/parts/p8-secular-form.tex#stepP:p8:id-avg@L192-L192 | difference equals ¦sum p¦^2/(2 m0)
EDGE: bpP:p8:conv#data | blueprint-P/parts/p8-secular-form.tex#stepP:p8:id-avg@L192-L192 | kappa=G m0 and a_i
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8
REVIEWER: sol-review-P-j
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p8:id-int
KIND: step
TITLE: Integrability
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:id-int@L193-L193
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:id-int@L193-L193
CONTRACT_ID: stepP:p8:id-int
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: bounded continuous functions are integrable on the compact torus; on N_R(rho_*) hat f continuous on the torus
SOURCE_QUANTIFIERS: w'
SOURCE_CONCLUSION: integrability of hat f_fix is equivalent to that of hat f_mov and the averages subtract; on N_R(rho_*) both integrable
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p8:id-diff, bpP:p8:perturbation-analytic, bpP:p8:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p8:id-diff | blueprint-P/parts/p8-secular-form.tex#stepP:p8:id-int@L193-L193 | continuity of the difference
EDGE: bpP:p8:perturbation-analytic | blueprint-P/parts/p8-secular-form.tex#stepP:p8:id-int@L193-L193 | (a): hat f continuous on the torus for w' in N_R(rho_*)
EDGE: bpP:p8:conv#data | blueprint-P/parts/p8-secular-form.tex#stepP:p8:id-int@L193-L193 | the Bochner averages S_fix, S_mov and the domain N_R(rho_*)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8+sol-review-P-j
REVIEWER: sol-delta-P-j
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p8:same-jets
KIND: corollary
TITLE: Same jets, same quadratic form, same Hamilton equations
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#bpP:p8:same-jets@L196-L204
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#bpP:p8:same-jets@L205-L207
CONTRACT_ID: bpP:p8:same-jets
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: on N_R(rho_*); alpha!=0 multi-index in (xi,eta); for (c): HasBirkhoff(P_mov,V,r_0,mu_0,P_0,Omega,beta) (Definition birkhoff), P_mov=hat f_mov, P_fix=hat f_fix assembled by the dictionary, points (I,p,q)=(Lambda,eta,xi) with I in V, p_j^2+q_j^2<r_0^2 in N_R(rho_*)
SOURCE_QUANTIFIERS: data of conv#data; rho_*; alpha; Lambda-derivatives
SOURCE_CONCLUSION: d^alpha_{(xi,eta)} S_mov=d^alpha S_fix for all alpha!=0 and Lambda-derivatives; (a) S_mov=C_0+delta+xi^T Q_h xi+eta^T Q_h eta+O(¦(xi,eta)¦^4), same Q_h, sigma_j, Omega_j, quartic jets coincide; (b) for mu=eps the secular equations of the two models coincide, Lambda constant, frequencies differ by mu d_{Lambda_i} delta; (c) HasBirkhoff(P_fix,V,r_0,mu_0,P_0-delta,Omega,beta) holds and conversely, beta hypotheses (H5),(H6) literally the same; S_mov o chi-S_fix o chi=delta(Lambda) for slow-variable symplectic chi(Lambda;.)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p8:same-jets#jets, bpP:p8:same-jets#transfer, bpP:p8:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p8:same-jets#jets | blueprint-P/parts/p8-secular-form.tex#bpP:p8:same-jets@L206-L206 | proof: derivatives of the difference and (a),(b)
EDGE: bpP:p8:same-jets#transfer | blueprint-P/parts/p8-secular-form.tex#bpP:p8:same-jets@L206-L206 | proof: (c) transfer to the frozen Birkhoff form
EDGE: bpP:p8:conv#data | blueprint-P/parts/p8-secular-form.tex#bpP:p8:same-jets@L197-L197 | S_fix, S_mov, N_R, dictionary
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8
REVIEWER: sol-review-P-j
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: audit S8-J PASS WITH NOTES: same_jets/same_jets_transfer cover jets and (c) transfer only; (a),(b) and composition clause not stated
NOTE: edge to bpP:p8:quartic deleted (the coincidence of the quartic jets is a consequence of the all-order equality here; Prop quartic depends on this corollary, not conversely). Two step nodes #jets, #transfer added for the unmarked proof obligations

NODE: bpP:p8:same-jets#jets
KIND: step
TITLE: All-order equality of the jets; same quadratic form; same equations
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#bpP:p8:same-jets#jets@L206-L206
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#bpP:p8:same-jets#jets@L206-L206
CONTRACT_ID: bpP:p8:same-jets#jets
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: delta does not depend on (xi,eta); Thm identification; Thm quadratic-form; Thm product-chart (d)
SOURCE_QUANTIFIERS: alpha!=0; (xi,Lambda,eta) in N_R(rho_*)
SOURCE_CONCLUSION: all (xi,eta)-derivatives of order >=1 of S_mov-S_fix vanish; (a) same quadratic form Q_h and constant C_0+delta; (b) for mu=eps, same secular equations, frequencies differ by mu d_Lambda delta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p8:identification, bpP:p8:quadratic-form, bpP:p7:product-chart, bpP:p8:perturbation-analytic, bpP:p8:conv#data, bpP:p8:coeffs
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p8:identification | blueprint-P/parts/p8-secular-form.tex#bpP:p8:same-jets#jets@L206-L206 | S_mov=S_fix+delta(Lambda) with delta independent of (xi,eta)
EDGE: bpP:p8:quadratic-form | blueprint-P/parts/p8-secular-form.tex#bpP:p8:same-jets#jets@L206-L206 | (a): the quadratic form Q_h
EDGE: bpP:p7:product-chart | blueprint-P/parts/p8-secular-form.tex#bpP:p8:same-jets#jets@L206-L206 | (d): Hamilton equations in the chart
EDGE: bpP:p8:perturbation-analytic | blueprint-P/parts/p8-secular-form.tex#bpP:p8:same-jets#jets@L206-L206 | S_fix, S_mov analytic so derivatives exist
EDGE: bpP:p8:conv#data | blueprint-P/parts/p8-secular-form.tex#bpP:p8:same-jets#jets@L206-L206 | S_fix, S_mov, the slow variables and N_R(rho_*)
EDGE: bpP:p8:coeffs | blueprint-P/parts/p8-secular-form.tex#bpP:p8:same-jets#jets@L206-L206 | C_0 and Q_h in the common quadratic form
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8+sol-delta-P-j
REVIEWER: sol-delta2-P-t
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: audit S8-J PASS WITH NOTES: same_jets_on states only the all-order jet equality; (a) same quadratic form and (b) same equations not stated
NOTE: added step: the all-order equality and (a),(b) are consumed by Parts 11b/12; proof paragraph L206

NODE: bpP:p8:same-jets#transfer
KIND: step
TITLE: Transfer to the frozen Birkhoff form (c)
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#bpP:p8:same-jets#transfer@L206-L206
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#bpP:p8:same-jets#transfer@L206-L206
CONTRACT_ID: bpP:p8:same-jets#transfer
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: data of conv#data; P_mov=hat f_mov and P_fix=hat f_fix with no mu dependence, assembled by (I,p,q)=(Lambda,eta,xi); HasBirkhoff(P_mov,V,r_0,mu_0,P_0,Omega,beta); for every I in V and p,q with p_j^2+q_j^2<r_0^2 for all j, (I,p,q) lies in N_R(rho_*); for the composition clause chi(Lambda;.) is a slow-variable symplectic change acting only on (xi,eta)
SOURCE_QUANTIFIERS: V, r_0, mu_0, P_0, Omega, beta
SOURCE_CONCLUSION: HasBirkhoff(P_fix,V,r_0,mu_0,P_0-delta,Omega,beta) and conversely: integrability clause (i) transfers and the expansion clause (ii) with P_0->P_0-delta; Omega, beta unchanged; for the composition clause, S_mov o chi-S_fix o chi=delta(Lambda)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p8:identification, bpP:p0:birkhoff#HasSecularBirkhoffForm, bpP:p0:secavg#secularAverage, bpP:p8:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p8:identification | blueprint-P/parts/p8-secular-form.tex#bpP:p8:same-jets#transfer@L206-L206 | P_av^mov-P_av^fix=delta(I) on the integrability set
EDGE: bpP:p0:birkhoff#HasSecularBirkhoffForm | blueprint-P/parts/p8-secular-form.tex#bpP:p8:same-jets#transfer@L206-L206 | definition of HasBirkhoff, clauses (i), (ii)
EDGE: bpP:p0:secavg#secularAverage | blueprint-P/parts/p8-secular-form.tex#bpP:p8:same-jets#transfer@L206-L206 | frozen average, I=Lambda
EDGE: bpP:p8:conv#data | blueprint-P/parts/p8-secular-form.tex#bpP:p8:same-jets#transfer@L206-L206 | dictionary (I,p,q)=(Lambda,eta,xi)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8+sol-delta-P-j
REVIEWER: sol-delta2-P-t
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: audit S8-J PASS WITH NOTES: same_jets_transfer proves the HasBirkhoff transfer but not the composition clause S_mov o chi - S_fix o chi = delta
NOTE: added step for the unmarked substantive transfer (c)

NODE: bpP:p8:quartic
KIND: proposition
TITLE: Quartic jet
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#bpP:p8:quartic@L216-L229
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#bpP:p8:quartic@L230-L235
CONTRACT_ID: bpP:p8:quartic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n>=2; Lambda with (xi,Lambda,eta) in N_R(rho_*)-range; v the eccentricity vectors of Definition poincare-def
SOURCE_QUANTIFIERS: n,m,kappa,a*; Lambda; for (a): alpha,v_i,v_j in the domain D
SOURCE_CONCLUSION: degree-four part of S_fix (and S_mov) is Q_4=sum_{i<j}[c1 ¦u_i¦^4+c2 ¦u_j¦^4+c3 ¦u_i¦^2¦u_j¦^2+c4 (u_i.u_j)^2+c5 ¦u_i¦^2 u_i.u_j+c6 ¦u_j¦^2 u_i.u_j] with c_nu(Lambda_i,Lambda_j) real analytic; (a) S_ij=-G m_i m_j a_j^-1 W(alpha_ij;v_i,v_j) with W real analytic on D={(alpha,v_i,v_j): 0<alpha<1, ¦v_i¦,¦v_j¦<1/4, alpha(1+¦v_i¦)<1-¦v_j¦}, independent of m,G,kappa, exact passage v_i=sqrt(1-¦u_i¦^2/(4 Lambda_i)) u_i/sqrt(Lambda_i); if W_2=A ¦v_i¦^2+A' ¦v_j¦^2+B v_i.v_j, then Q_4^(ij)=(-G m_i m_j/a_j)[W_4(u_i/sqrt(Lambda_i),u_j/sqrt(Lambda_j))-A ¦u_i¦^4/(4 Lambda_i^2)-A' ¦u_j¦^4/(4 Lambda_j^2)-(B/8)(u_i.u_j)/sqrt(Lambda_i Lambda_j)(¦u_i¦^2/Lambda_i+¦u_j¦^2/Lambda_j)]; sufficient subdomain ¦v_i¦,¦v_j¦<min(1/4,(1-alpha)/(1+alpha)); Taylor coefficients of W at v=0 real analytic for every alpha in (0,1), with convergence neighbourhood allowed to shrink as alpha->1; (b) c_1,c_2 = -G m_i m_j (h^(4)(0)/64-h''(0)/16)/Lambda^2 with h(eps)=Phi(a(1-eps),a')(1-eps); (c) c_1=m_i m_j r_1^ex(a_i,a_j)/(2 Lambda_i^2), c_2 analogously, with r_1^ex=-h^(4)(0)/32+h''(0)/8 (G=m0=1); explicit c_3..c_6 are forward obligations of Part 11b
CONSTANT_SCOPE: c_nu depend only on (Lambda_i,Lambda_j) (and m,G,kappa); W independent of m,G,kappa
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p8:q4-str, stepP:p8:q4-a, stepP:p8:q4-b, stepP:p8:q4-c, bpP:p8:same-jets, bpP:p7:poincare-def, bpP:p8:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p8:q4-str | blueprint-P/parts/p8-secular-form.tex#bpP:p8:quartic@L231-L231 | proof step Structure
EDGE: stepP:p8:q4-a | blueprint-P/parts/p8-secular-form.tex#bpP:p8:quartic@L232-L232 | proof step (a)
EDGE: stepP:p8:q4-b | blueprint-P/parts/p8-secular-form.tex#bpP:p8:quartic@L233-L233 | proof step (b)
EDGE: stepP:p8:q4-c | blueprint-P/parts/p8-secular-form.tex#bpP:p8:quartic@L234-L234 | proof step (c)
EDGE: bpP:p8:same-jets | blueprint-P/parts/p8-secular-form.tex#bpP:p8:quartic@L217-L217 | S_mov has the same degree-four part
EDGE: bpP:p7:poincare-def | blueprint-P/parts/p8-secular-form.tex#bpP:p8:quartic@L221-L221 | v of Definition poincare-def
EDGE: bpP:p8:conv#data | blueprint-P/parts/p8-secular-form.tex#bpP:p8:quartic@L217-L217 | data, N_R(rho_*), S_fix
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8+sol-review-P-j
REVIEWER: sol-delta-P-j
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: quartic/quartic_scaling/quartic_pair_scaling cover q4-str,a,b but not (c) r_1^ex identification, S_mov same-jets or the sufficient-subdomain clause; audit S8-4 PASS WITH NOTES for the package, parent conclusion not fully stated
NOTE: edge to bpP:p8:cp11-check deleted (remark comparing CP11 (B.6); no proof consumes it; it depends on this proposition). Edges to evenness/quadratic-form/perturbation-analytic are carried by the steps

NODE: stepP:p8:q4-str
KIND: step
TITLE: Structure
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:q4-str@L231-L231
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:q4-str@L231-L231
CONTRACT_ID: stepP:p8:q4-str
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Cor evenness; Prop perturbation-analytic; pair decomposition (Step qf-pair)
SOURCE_QUANTIFIERS: (xi,Lambda,eta) in N_R(rho_*)
SOURCE_CONCLUSION: the degree-four part is an O(2)-invariant polynomial analytic in Lambda, a sum over pairs of degree-two polynomials in ¦u_i¦^2,¦u_j¦^2,u_i.u_j: the six listed monomials
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p8:evenness, bpP:p8:perturbation-analytic, stepP:p8:qf-pair, bpP:p8:e-weyl, bpP:p8:e-taylor, bpP:p8:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p8:evenness | blueprint-P/parts/p8-secular-form.tex#stepP:p8:q4-str@L231-L231 | even, O(2)-invariant Taylor parts
EDGE: bpP:p8:perturbation-analytic | blueprint-P/parts/p8-secular-form.tex#stepP:p8:q4-str@L231-L231 | joint analyticity (Taylor coefficients analytic in Lambda)
EDGE: stepP:p8:qf-pair | blueprint-P/parts/p8-secular-form.tex#stepP:p8:q4-str@L231-L231 | pair decomposition
EDGE: bpP:p8:e-weyl | blueprint-P/parts/p8-secular-form.tex#stepP:p8:q4-str@L231-L231 | invariants are polynomials in dot products
EDGE: bpP:p8:e-taylor | blueprint-P/parts/p8-secular-form.tex#stepP:p8:q4-str@L231-L231 | Taylor coefficients of a jointly analytic function
EDGE: bpP:p8:conv#data | blueprint-P/parts/p8-secular-form.tex#stepP:p8:q4-str@L231-L231 | S_fix, u_i and N_R(rho_*) for the quartic Taylor part
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8+sol-review-P-j
REVIEWER: sol-delta-P-j
LEAN_STATUS: PROVED
LEAN_REF: quartic (KAM/Planetary/SecularForm/Quartic.lean)
LEAN_NOTE: audit S8-4 round 3 PASS WITH NOTES; quartic gives six analytic coefficients and the pair-sum quartic part
NOTE: -

NODE: stepP:p8:q4-a
KIND: step
TITLE: (a)
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:q4-a@L232-L232
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:q4-a@L232-L232
CONTRACT_ID: stepP:p8:q4-a
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: q^(i)=a_i tilde q(lambda_i,v_i) with tilde q independent of a,m,kappa; D={(alpha,v_i,v_j): 0<alpha<1, ¦v_i¦,¦v_j¦<1/4, alpha(1+¦v_i¦)<1-¦v_j¦} (disjoint ellipses)
SOURCE_QUANTIFIERS: alpha in (0,1); v_i,v_j in D
SOURCE_CONCLUSION: S_ij=-G m_i m_j a_j^-1 W(alpha;v_i,v_j) with W real analytic on D, independent of m,G,kappa; Taylor coefficients at v=0 analytic for all alpha in (0,1); exact passage v_i=sqrt(1-¦u_i¦^2/(4 Lambda_i)) u_i/sqrt(Lambda_i); if W_2=A ¦v_i¦^2+A' ¦v_j¦^2+B v_i.v_j, then Q_4^(ij)=(-G m_i m_j/a_j)[W_4(u_i/sqrt(Lambda_i),u_j/sqrt(Lambda_j))-A ¦u_i¦^4/(4 Lambda_i^2)-A' ¦u_j¦^4/(4 Lambda_j^2)-(B/8)(u_i.u_j)/sqrt(Lambda_i Lambda_j)(¦u_i¦^2/Lambda_i+¦u_j¦^2/Lambda_j)] via the expansion of (1-t)^(1/2)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p7:poincare-def, bpP:p8:perturbation-analytic, stepP:p8:pa-circ, bpP:p8:e-taylor, stepP:p8:qf-pair, bpP:p8:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p7:poincare-def | blueprint-P/parts/p8-secular-form.tex#stepP:p8:q4-a@L232-L232 | q^(i)=a_i tilde q(lambda_i,v_i), v in terms of u
EDGE: bpP:p8:perturbation-analytic | blueprint-P/parts/p8-secular-form.tex#stepP:p8:q4-a@L232-L232 | the argument of the proposition applies on D (positive lower bound of the distance)
EDGE: stepP:p8:pa-circ | blueprint-P/parts/p8-secular-form.tex#stepP:p8:q4-a@L232-L232 | Taylor coefficients at v=0 are those of the circular case
EDGE: bpP:p8:e-taylor | blueprint-P/parts/p8-secular-form.tex#stepP:p8:q4-a@L232-L232 | Taylor expansion of (1-t)^(1/2), t=¦u¦^2/(4 Lambda)
EDGE: stepP:p8:qf-pair | blueprint-P/parts/p8-secular-form.tex#stepP:p8:q4-a@L232-L232 | V_ij, S_ij
EDGE: bpP:p8:conv#data | blueprint-P/parts/p8-secular-form.tex#stepP:p8:q4-a@L232-L232 | the secular slow variables u_i=(xi_i,eta_i) and their actions Lambda_i in the conversion
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8+sol-review-P-j
REVIEWER: sol-delta-P-j
LEAN_STATUS: PROVED
LEAN_REF: quartic_pair_scaling (KAM/Planetary/SecularForm/Quartic/PairScaling.lean); quartic_scaling (KAM/Planetary/SecularForm/Quartic/Scaling.lean); quartic_pair_chart_conversion (KAM/Planetary/SecularForm/Quartic/PairChart.lean); quartic_sqrt_chart_conversion_const (KAM/Planetary/SecularForm/Quartic/Conversion.lean)
LEAN_NOTE: audit S8-4 round 3 PASS WITH NOTES (F2 closed); composite: scaling form, analyticity of W on separatedDomain, literal Q4 conversion with A,A',B corrections
NOTE: -

NODE: stepP:p8:q4-b
KIND: step
TITLE: (b)
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:q4-b@L233-L233
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:q4-b@L233-L233
CONTRACT_ID: stepP:p8:q4-b
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u_j=0; Step qf-diag computation; E=¦u¦^2/Lambda-¦u¦^4/(4 Lambda^2)
SOURCE_QUANTIFIERS: i!=j
SOURCE_CONCLUSION: coefficient of E^2 is h^(4)(0)/64, so the ¦u¦^4 coefficient is -G m_i m_j (h^(4)/64-h''/16)/Lambda^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p8:qf-diag, bpP:p8:e-taylor, bpP:p8:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p8:qf-diag | blueprint-P/parts/p8-secular-form.tex#stepP:p8:q4-b@L233-L233 | S_ij at u_j=0 as sum over E^l h^(2l)(0) binomial moments
EDGE: bpP:p8:e-taylor | blueprint-P/parts/p8-secular-form.tex#stepP:p8:q4-b@L233-L233 | Taylor expansion of h and E in ¦u¦
EDGE: bpP:p8:conv#data | blueprint-P/parts/p8-secular-form.tex#stepP:p8:q4-b@L233-L233 | u_i=(xi_i,eta_i) and Gamma_i=¦u_i¦^2/2 in the exact expression for E
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8+sol-review-P-j
REVIEWER: sol-delta-P-j
LEAN_STATUS: PROVED
LEAN_REF: quartic (KAM/Planetary/SecularForm/Quartic.lean); quarticCoeff_zero, quarticCoeff_one (KAM/Planetary/SecularForm/Quartic/Diagonal.lean)
LEAN_NOTE: audit S8-4 round 3 PASS WITH NOTES; third conjunct of quartic gives c_1,c_2 = -G m_i m_j (h''''/64 - h''/16)/Lambda^2
NOTE: -

NODE: stepP:p8:q4-c
KIND: step
TITLE: (c)
STATEMENT_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:q4-c@L234-L234
PROOF_SOURCE: blueprint-P/parts/p8-secular-form.tex#stepP:p8:q4-c@L234-L234
CONTRACT_ID: stepP:p8:q4-c
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: step (b); definition r_1^ex=-h^(4)(0)/32+h''(0)/8 (G=m0=1)
SOURCE_QUANTIFIERS: pairs i<j
SOURCE_CONCLUSION: c_1,c_2 equal m_i m_j r_1^ex/(2 Lambda^2); the mixed coefficients c_3..c_6 are not computed here (forward obligation of Part 11b); comparison with the printed CP11 r_1 is not asserted
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p8:q4-b
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p8:q4-b | blueprint-P/parts/p8-secular-form.tex#stepP:p8:q4-c@L234-L234 | identification of c_1,c_2 with r_1^ex is (b)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p8
REVIEWER: sol-review-P-j
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: radialR1 is only a def (Defs.lean); no theorem identifies c_1,c_2 with m_i m_j r_1^ex/(2 Lambda^2); S8-4 handoff: no theorem about radialR1
NOTE: the CP11 (B.6) comparison (equality of the repaired formula with r_1^ex, certificate in Remark cp11-check) is provenance/comparison and is not consumed: no edge

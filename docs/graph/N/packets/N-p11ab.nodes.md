NODE: bpN:p11:ext-num
KIND: external
TITLE: Numerics
STATEMENT_SOURCE: blueprint-N/parts/p11a-partial-route.tex#bpN:p11:ext-num@L40-L40
PROOF_SOURCE: -
CONTRACT_ID: bpN:p11:ext-num
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: real numbers x, beta<gamma
SOURCE_QUANTIFIERS: x in (0,1); 0<beta<gamma
SOURCE_CONCLUSION: e>2.718, 2/e<0.736, 1/e<0.368; coth(x)>1 for x>0; for 0<beta<gamma and x in (0,1): x^gamma<x^beta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab
REVIEWER: sol-review-N-f
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external (E1) of Part 11

NODE: bpN:p11:ext-rpow
KIND: external
TITLE: Powers
STATEMENT_SOURCE: blueprint-N/parts/p11a-partial-route.tex#bpN:p11:ext-rpow@L41-L41
PROOF_SOURCE: -
CONTRACT_ID: bpN:p11:ext-rpow
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: x>0, real alpha, beta; epsilon>0
SOURCE_QUANTIFIERS: x; alpha, beta; y
SOURCE_CONCLUSION: x^alpha x^beta=x^(alpha+beta), (x^alpha)^(-1)=x^(-alpha), x->x^alpha monotone (increasing for alpha>0); exp(y)>=1+y>=y; exp(epsilon y)/y^N -> infinity as y -> infinity for epsilon>0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab
REVIEWER: sol-review-N-f
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external (E2) of Part 11 (the Mathlib names in the text are hints, not source premises)

NODE: bpN:p11:ext-chain
KIND: external
TITLE: Chain rule for a linear change of variables and for differentiable curves
STATEMENT_SOURCE: blueprint-N/parts/p11a-partial-route.tex#bpN:p11:ext-chain@L42-L42
PROOF_SOURCE: -
CONTRACT_ID: bpN:p11:ext-chain
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: differentiable maps; a linear change of variables; differentiable curves
SOURCE_QUANTIFIERS: maps and curves as in each form
SOURCE_CONCLUSION: chain rule for a linear change of variables and for differentiable curves
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab
REVIEWER: sol-review-N-f
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external (E3) of Part 11; stays an external per SPEC (the Kref to K:bp:p1:ext-mvt is a pointer to the related mean value inequality, not a restatement); consumed by stepN:p11:or-chain, bpN:p11:symplectic (chain rule) and, in Part 11c, stepN:p11:cj

NODE: bpN:p11:wfield
KIND: definition
TITLE: Weighted Hamiltonian field
STATEMENT_SOURCE: blueprint-N/parts/p11a-partial-route.tex#bpN:p11:wfield@L48-L56
PROOF_SOURCE: -
CONTRACT_ID: bpN:p11:wfield
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: c>0; Hhat: R^n x R^n x R^k x R^k -> R differentiable at y=(theta,I;q,p) (holomorphic u,v for the complex bracket)
SOURCE_QUANTIFIERS: c; Hhat; y (resp. u, v)
SOURCE_CONCLUSION: defines X^c_Hhat(y)=(d_I Hhat, -d_theta Hhat, c d_p Hhat, -c d_q Hhat), the bracket {u,v}_c = d_theta u . d_I v - d_I u . d_theta v + c(d_q u . d_p v - d_p u . d_q v) = Du . X^c_v (antisymmetric, also for holomorphic u,v with complex partials), and Omega_c=diag(J_n,cJ_k) with X^c_u=Omega_c grad u
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab
REVIEWER: sol-review-N-f
LEAN_STATUS: PROVED
LEAN_REF: wfield, realWfield, extBracket (KAM/Nekhoroshev/Partial/Setting.lean)
LEAN_NOTE: audit N11-A-audit-1 PASS WITH NOTES
NOTE: package bpN:p11:wfield (SPEC); c=1 with k=0 is Definition bpN:p5:setting, a comparison only (no edge)

NODE: bpN:p11:orbit
KIND: lemma
TITLE: Period conversion with slow variables
STATEMENT_SOURCE: blueprint-N/parts/p11a-partial-route.tex#bpN:p11:orbit@L58-L61
PROOF_SOURCE: blueprint-N/parts/p11a-partial-route.tex#bpN:p11:orbit@L62-L65
CONTRACT_ID: bpN:p11:orbit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: H: Ph_{n+k} -> R; Hhat(theta,I;q,p)=(1/2pi)H((2 pi theta,q),(I,p)); Theta((phi_f,q),(I,p))=(phi_f/2pi,I;q,p); a curve z and a time t with H differentiable at z(t)
SOURCE_QUANTIFIERS: n,k; H; z; t
SOURCE_CONCLUSION: z'(t)=X_H(z(t)) iff y=Theta o z satisfies y'(t)=X^{2pi}_Hhat(y(t)) (Hhat differentiable at y(t)); Theta and Theta^{-1} are linear isomorphisms; fast actions, slow variables and time unchanged, fast angles divided by 2 pi
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p11:or-chain, stepN:p11:or-eq, bpN:p11:wfield, bpN:p0:vf#hamiltonianVectorField, bpN:p0:partial-sec#Phase
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p11:or-chain | blueprint-N/parts/p11a-partial-route.tex#bpN:p11:orbit@L63-L63 | proof step (chain rule)
EDGE: stepN:p11:or-eq | blueprint-N/parts/p11a-partial-route.tex#bpN:p11:orbit@L64-L64 | proof step (the equations)
EDGE: bpN:p11:wfield | blueprint-N/parts/p11a-partial-route.tex#bpN:p11:orbit@L59-L59 | X^{2pi}_Hhat is the weight-2pi field of Definition wfield
EDGE: bpN:p0:vf#hamiltonianVectorField | blueprint-N/parts/p11a-partial-route.tex#bpN:p11:orbit@L59-L59 | z'=X_H(z) with the frozen field of Ph_{n+k}
EDGE: bpN:p0:partial-sec#Phase | blueprint-N/parts/p11a-partial-route.tex#bpN:p11:orbit@L58-L58 | H is defined on Ph_{n+k}, Theta on its coordinates
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab
REVIEWER: sol-review-N-f
LEAN_STATUS: PROVED
LEAN_REF: orbit, theta, thetaInv, converted, thetaCLM, thetaInvCLM (KAM/Nekhoroshev/Partial/Coordinates.lean)
LEAN_NOTE: audit N11-A PASS WITH NOTES; signed iff theorem; Theta/Theta^{-1} as continuous linear equivalences
NOTE: forward note: Lemma bpN:p1:period-convert (k=0, opposite normalisation) is a comparison, no edge; consumed by stepN:p11:final-orbit

NODE: stepN:p11:or-chain
KIND: step
TITLE: Chain rule
STATEMENT_SOURCE: blueprint-N/parts/p11a-partial-route.tex#stepN:p11:or-chain@L63-L63
PROOF_SOURCE: blueprint-N/parts/p11a-partial-route.tex#stepN:p11:or-chain@L63-L63
CONTRACT_ID: stepN:p11:or-chain
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Hhat=(1/2pi)H o Theta^{-1} with Theta^{-1}(theta,I;q,p)=((2 pi theta,q),(I,p)) linear
SOURCE_QUANTIFIERS: z; t
SOURCE_CONCLUSION: Hhat is differentiable at Theta z iff H at z; d_theta Hhat=d_{phi_f}H, d_I Hhat=(1/2pi)d_I H, d_q Hhat=(1/2pi)d_q H, d_p Hhat=(1/2pi)d_p H
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:ext-chain
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:ext-chain | blueprint-N/parts/p11a-partial-route.tex#stepN:p11:or-chain@L63-L63 | chain rule for the linear change of variables Theta
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab
REVIEWER: sol-review-N-f
LEAN_STATUS: PROVED
LEAN_REF: orbit, theta, thetaInv, converted (KAM/Nekhoroshev/Partial/Coordinates.lean)
LEAN_NOTE: audit N11-A-audit-1 PASS WITH NOTES; internal to bpN:p11:orbit
NOTE: -

NODE: stepN:p11:or-eq
KIND: step
TITLE: Equations
STATEMENT_SOURCE: blueprint-N/parts/p11a-partial-route.tex#stepN:p11:or-eq@L64-L64
PROOF_SOURCE: blueprint-N/parts/p11a-partial-route.tex#stepN:p11:or-eq@L64-L64
CONTRACT_ID: stepN:p11:or-eq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: frozen field X_H=(d_I H,-d_phi H) on Ph_{n+k}; the partials of step or-chain
SOURCE_QUANTIFIERS: z; t
SOURCE_CONCLUSION: the components theta'=d_I Hhat, I'=-d_theta Hhat, q'=2 pi d_p Hhat, p'=-2 pi d_q Hhat of X^{2pi}_Hhat; the computation reverses (converse)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p0:vf#hamiltonianVectorField, stepN:p11:or-chain, bpN:p11:wfield
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p0:vf#hamiltonianVectorField | blueprint-N/parts/p11a-partial-route.tex#stepN:p11:or-eq@L64-L64 | the frozen field X_H=(d_I H,-d_phi H) for Ph_{n+k}
EDGE: stepN:p11:or-chain | blueprint-N/parts/p11a-partial-route.tex#stepN:p11:or-eq@L64-L64 | the partials of Hhat in terms of those of H
EDGE: bpN:p11:wfield | blueprint-N/parts/p11a-partial-route.tex#stepN:p11:or-eq@L64-L64 | these are the components of X^{2pi}_Hhat
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab
REVIEWER: sol-review-N-f
LEAN_STATUS: PROVED
LEAN_REF: realWfield_converted (KAM/Nekhoroshev/Partial/Coordinates.lean)
LEAN_NOTE: audit N11-A PASS WITH NOTES; component identity realWfield(2pi)(converted H)(theta z)=theta(X_H z), converse via orbit
NOTE: -

NODE: bpN:p11:exponents
KIND: lemma
TITLE: Exponents
STATEMENT_SOURCE: blueprint-N/parts/p11a-partial-route.tex#bpN:p11:exponents@L67-L69
PROOF_SOURCE: blueprint-N/parts/p11a-partial-route.tex#bpN:p11:exponents@L70-L73
CONTRACT_ID: bpN:p11:exponents
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n>=2; a_n=2/(6n^2-3n+14), b_n=3/(6n^2-3n+14) as in Definition partial-exponents
SOURCE_QUANTIFIERS: n
SOURCE_CONCLUSION: 0<a_n<b_n<1/(2n) and 2 b_n<1/(2n); hence gamma_1=1/(2n)-2b_n>0, gamma_2=1/(2n)-b_n>0, gamma_3=1/(2n)-a_n>0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p11:ex-den, stepN:p11:ex-cmp, bpN:p0:partial-exponents#partialTimeExponent, bpN:p0:partial-exponents#partialDriftExponent
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p11:ex-den | blueprint-N/parts/p11a-partial-route.tex#bpN:p11:exponents@L71-L71 | proof step (denominator)
EDGE: stepN:p11:ex-cmp | blueprint-N/parts/p11a-partial-route.tex#bpN:p11:exponents@L72-L72 | proof step (comparison)
EDGE: bpN:p0:partial-exponents#partialTimeExponent | blueprint-N/parts/p11a-partial-route.tex#bpN:p11:exponents@L68-L68 | a_n of the frozen statement
EDGE: bpN:p0:partial-exponents#partialDriftExponent | blueprint-N/parts/p11a-partial-route.tex#bpN:p11:exponents@L68-L68 | b_n of the frozen statement
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab
REVIEWER: sol-review-N-f
LEAN_STATUS: PROVED
LEAN_REF: exponents (KAM/Nekhoroshev/Partial/Constants.lean)
LEAN_NOTE: audit N11-B math PASS (audit 1; F1 naming finding overruled by orchestrator ruling); ex-den/ex-cmp internal
NOTE: -

NODE: stepN:p11:ex-den
KIND: step
TITLE: Denominator
STATEMENT_SOURCE: blueprint-N/parts/p11a-partial-route.tex#stepN:p11:ex-den@L71-L71
PROOF_SOURCE: blueprint-N/parts/p11a-partial-route.tex#stepN:p11:ex-den@L71-L71
CONTRACT_ID: stepN:p11:ex-den
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n>=2
SOURCE_QUANTIFIERS: n
SOURCE_CONCLUSION: q_n=6n^2-3n+14>=32>0 and a_n<b_n (2<3)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p0:partial-exponents#partialTimeExponent, bpN:p0:partial-exponents#partialDriftExponent
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p0:partial-exponents#partialTimeExponent | blueprint-N/parts/p11a-partial-route.tex#stepN:p11:ex-den@L71-L71 | a_n=2/q_n
EDGE: bpN:p0:partial-exponents#partialDriftExponent | blueprint-N/parts/p11a-partial-route.tex#stepN:p11:ex-den@L71-L71 | b_n=3/q_n
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab
REVIEWER: sol-review-N-f
LEAN_STATUS: PROVED
LEAN_REF: exponents (KAM/Nekhoroshev/Partial/Constants.lean)
LEAN_NOTE: audit N11-B-audit-1 PASS (ruling N11-B-audit-1-ruling); internal to bpN:p11:exponents
NOTE: -

NODE: stepN:p11:ex-cmp
KIND: step
TITLE: Comparison
STATEMENT_SOURCE: blueprint-N/parts/p11a-partial-route.tex#stepN:p11:ex-cmp@L72-L72
PROOF_SOURCE: blueprint-N/parts/p11a-partial-route.tex#stepN:p11:ex-cmp@L72-L72
CONTRACT_ID: stepN:p11:ex-cmp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:exponents; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: n
SOURCE_CONCLUSION: 2 b_n<1/(2n) iff 6n^2-15n+14>0 (true); hence a_n<b_n<2b_n<1/(2n)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p11:ex-den, bpN:p0:partial-exponents#partialDriftExponent, bpN:p0:partial-exponents#partialTimeExponent
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p11:ex-den | blueprint-N/parts/p11a-partial-route.tex#stepN:p11:ex-cmp@L72-L72 | q_n>0 and a_n<b_n
EDGE: bpN:p0:partial-exponents#partialDriftExponent | blueprint-N/parts/p11a-partial-route.tex#stepN:p11:ex-cmp@L72-L72 | b_n
EDGE: bpN:p0:partial-exponents#partialTimeExponent | blueprint-N/parts/p11a-partial-route.tex#stepN:p11:ex-cmp@L72-L72 | a_n in the concluding comparison is the frozen time exponent 2/(6n^2-3n+14)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab+sol-delta-N-f
REVIEWER: sol-delta2-N-f
LEAN_STATUS: PROVED
LEAN_REF: exponents (KAM/Nekhoroshev/Partial/Constants.lean)
LEAN_NOTE: audit N11-B-audit-1 PASS (ruling N11-B-audit-1-ruling); internal to bpN:p11:exponents
NOTE: -

NODE: bpN:p11:constants
KIND: definition
TITLE: Data and constants of the stopped proof
STATEMENT_SOURCE: blueprint-N/parts/p11a-partial-route.tex#bpN:p11:constants@L77-L84
PROOF_SOURCE: -
CONTRACT_ID: bpN:p11:constants
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data n>=2, k>=1, G, G', D, rho, g, m, M_C, h of Theorem bpN:p0:partial with sigma in {1,-1} from HasDefiniteFastPart
SOURCE_QUANTIFIERS: n,k; G,G',D,rho,g,m,M_C,h (then sigma); mu>0
SOURCE_CONCLUSION: defines s=rho/(4 pi), m_1=m/(2 pi), M_1=M_C/(2 pi), g_1=g/(2 pi), r_0=min{rho/2,32g/m}, A=40M_1/m_1=40M_C/m, eps_0=m_1 r_0^2/(2^14 A^{2n}), R_0=r_0/A, kappa_C=coth(pi s)^n, c_K=(2 pi eps_0/kappa_C)^{1/(2n)}; for mu>0: eps(mu)=kappa_C mu/(2 pi), K(mu)=(eps_0/eps)^{1/(2n)}=c_K mu^{-1/(2n)} (when eps<=eps_0), d=mu^{b_n}, w=d/4, K_a=K/sqrt n, kappa=2 pi K_a s; threshold mu_0=min of mu_a..mu_f of Step final-mu; covering parameters p=9/8, q=9, b_c=1/32
CONSTANT_SCOPE: all of s, m_1, M_1, g_1, r_0, A, eps_0, R_0, kappa_C, c_K depend only on the data (n,k,G,G',D,rho,g,m,M_C,h); mu_0 is the minimum of mu_a..mu_f and depends only on the data; p=9/8, q=9, b_c=1/32 are absolute
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p0:partial-definite#HasDefiniteFastPart, bpN:p0:partial-exponents#partialDriftExponent
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p0:partial-definite#HasDefiniteFastPart | blueprint-N/parts/p11a-partial-route.tex#bpN:p11:constants@L78-L78 | sigma from HasDefiniteFastPart; the data g, m, h, rho
EDGE: bpN:p0:partial-exponents#partialDriftExponent | blueprint-N/parts/p11a-partial-route.tex#bpN:p11:constants@L81-L81 | d=mu^{b_n}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab
REVIEWER: sol-review-N-f
LEAN_STATUS: PROVED
LEAN_REF: PartialConstants, constants (KAM/Nekhoroshev/Partial/Constants.lean)
LEAN_NOTE: audit N11-B-audit-1 PASS (ruling N11-B-audit-1-ruling)
NOTE: package bpN:p11:constants (SPEC). Dropped candidate edges: stepN:p11:final-mu (forward pointer: it defines mu_0 and itself uses these constants; an edge would close a cycle), bpN:p11:b-change (explanatory remark: the values p,q,b_c are fixed in this definition), bpN:p11:hessian (the side claim A>=pM_1/(b_c m_1)+sqrt 2 is re-derived in Lemma block-data; hessian itself uses these constants), bpN:p9:setting (provenance)

NODE: bpN:p11:ext-class
KIND: definition
TITLE: Extended class $\Os Rs^{e}$, extended phase space, bracket
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:ext-class@L8-L14
PROOF_SOURCE: -
CONTRACT_ID: bpN:p11:ext-class
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpN:p11:s-ext-class#data; 0<R<=r_B
SOURCE_QUANTIFIERS: R in (0,r_B]; rho, sigma
SOURCE_CONCLUSION: defines D-hat={I_c} x S-tilde in C^n x C^{2k}, extended actions I-hat=(I,x-tilde) in C^{n+2k} (m=n+2k in Part 4), points y=(theta,I,x-tilde); D^e_{R,s}=T_s x V_R D-hat={¦Im theta¦<s, ¦I-I_c¦<R, dist_inf(x-tilde,S-tilde)<R}; O(R,s)^e, ¦u¦_{R,s} as in Definition p4:norm for D=D-hat; O^{e,R} real on W^e_R:=D^e_{R,s} cap R^{2n+2k}; the bracket {u,v}_c of Definition wfield in (theta,I,x-tilde); the conditions (SL)_{rho,sigma}: 16 k c sigma<=rho and (SL): c<=r_B/(32 k s) (iff 64 pi k s r_B<=w^2); (SL) implies (SL)_{rho,sigma} whenever sigma<=2 s rho/r_B
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p4:norm, bpN:p4:domains, bpN:p11:wfield, bpN:p11:s-ext-class#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p4:norm | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:ext-class@L9-L10 | the class O(R,s) and norm for D=D-hat
EDGE: bpN:p4:domains | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:ext-class@L9-L10 | V_R D-hat, D_{R,s}=T_s x V_R D-hat
EDGE: bpN:p11:wfield | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:ext-class@L10-L10 | the bracket {u,v}_c in the variables (theta,I,x-tilde)
EDGE: bpN:p11:s-ext-class#data | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:ext-class@L9-L11 | I_c, S-tilde, r_B, c (and lambda) of the block data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab
REVIEWER: sol-review-N-f
LEAN_STATUS: PROVED
LEAN_REF: ext_class, slowLoss, PartialBlock.base, PartialBlock.SL (KAM/Nekhoroshev/Partial/Setting.lean)
LEAN_NOTE: audit N11-A-audit-1 PASS WITH NOTES
NOTE: package bpN:p11:ext-class (SPEC); (SL) and (SL)_{rho,sigma} are items of this definition

NODE: bpN:p11:ext-part4
KIND: lemma
TITLE: Part~\ref{bpN:p4} for the extended class
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:ext-part4@L16-L18
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:ext-part4@L16-L18
CONTRACT_ID: bpN:p11:ext-part4
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a base set D-hat subset C^{n+2k} (Part 4 is proved for an arbitrary D subset C^m with m independent of n); the extended class O(.,s)^e
SOURCE_QUANTIFIERS: as in the six lemmas of Part 4
SOURCE_CONCLUSION: Lemmas bpN:p4:coefficients, sup-weighted, algebra, cauchy ((a) pointwise in I-hat; (b) with max_{i<=n+2k}), general-cauchy and projections hold for O(.,s)^e with the same constants
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:ext-class, bpN:p4:norm, bpN:p4:domains, bpN:p4:coefficients, bpN:p4:sup-weighted, bpN:p4:algebra, bpN:p4:cauchy, bpN:p4:general-cauchy, bpN:p4:projections
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:ext-part4@L16-L17 | the extended class and its norm
EDGE: bpN:p4:norm | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:ext-part4@L17-L17 | Part 4 norm for D-hat subset C^{n+2k}
EDGE: bpN:p4:domains | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:ext-part4@L17-L17 | V_R D-hat
EDGE: bpN:p4:coefficients | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:ext-part4@L16-L16 | statement of Lemma coefficients transferred to D-hat
EDGE: bpN:p4:sup-weighted | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:ext-part4@L16-L16 | statement of Lemma sup-weighted (B.1) transferred
EDGE: bpN:p4:algebra | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:ext-part4@L16-L16 | statement of Lemma algebra (B.2) transferred
EDGE: bpN:p4:cauchy | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:ext-part4@L16-L16 | statement of Lemma cauchy (B.3) transferred
EDGE: bpN:p4:general-cauchy | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:ext-part4@L16-L16 | statement of Lemma general-cauchy transferred
EDGE: bpN:p4:projections | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:ext-part4@L16-L16 | statement of Lemma projections transferred
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab
REVIEWER: sol-review-N-f
LEAN_STATUS: PROVED
LEAN_REF: ext_part4 (KAM/Nekhoroshev/Partial/Bracket.lean)
LEAN_NOTE: audit N11-C PASS WITH NOTES
NOTE: inline proof (proof source = statement): Part 4 holds for an arbitrary base set; only the bracket uses m=n (so bpN:p4:bracket is not used here)

NODE: bpN:p11:bracket
KIND: lemma
TITLE: Bracket estimate with slow pairs, B.4$^e$
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:bracket@L20-L24
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:bracket@L25-L29
CONTRACT_ID: bpN:p11:bracket
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u in O(R_0,s_0)^e, v in O(R,s)^e of finite norm; 0<rho<R, 0<sigma<s, R-rho<R_0, s-sigma<s_0; the extended class with weight c
SOURCE_QUANTIFIERS: R_0,s_0,R,s,rho,sigma; u,v
SOURCE_CONCLUSION: {u,v}_c in O(R-rho,s-sigma)^e and ¦{u,v}_c¦_{R-rho,s-sigma}<=[(1/e)(1/((R_0-R+rho)sigma)+1/((s_0-s+sigma)rho))+2kc/((R_0-R+rho)rho)]¦u¦_{R_0,s_0}¦v¦_{R,s}; under (SL)_{rho,sigma} the bracket in [ ] is <=(1/2)(1/((R_0-R+rho)sigma)+1/((s_0-s+sigma)rho)); pointwise values on D^e_{R-rho,s-sigma} are bounded by the weighted norm
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p11:br-fast, stepN:p11:br-slow, stepN:p11:br-dom, bpN:p11:ext-class, bpN:p11:wfield, bpN:p11:s-ext-class#data, bpN:p4:norm, bpN:p4:domains, bpN:p4:sup-weighted, bpN:p11:ext-part4
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p11:br-fast | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:bracket@L26-L26 | proof step (fast part)
EDGE: stepN:p11:br-slow | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:bracket@L27-L27 | proof step (slow part)
EDGE: stepN:p11:br-dom | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:bracket@L28-L28 | proof step (domination)
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:bracket@L21-L23 | the extended class, (SL)_{rho,sigma}
EDGE: bpN:p11:wfield | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:bracket@L21-L21 | the bracket {u,v}_c
EDGE: bpN:p11:s-ext-class#data | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:bracket@L22-L22 | the weight c and the pair count k
EDGE: bpN:p4:norm | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:bracket@L22-L22 | weighted norm ¦.¦_{R,s}
EDGE: bpN:p4:domains | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:bracket@L21-L21 | D^e_{R-rho,s-sigma}
EDGE: bpN:p4:sup-weighted | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:bracket@L23-L23 | pointwise values bounded by the weighted norm (Lemma sup-weighted(a))
EDGE: bpN:p11:ext-part4 | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:bracket@L23-L23 | sup-weighted(a) for the extended class
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab
REVIEWER: sol-review-N-f
LEAN_STATUS: PROVED
LEAN_REF: bracket, bracket_dominated (KAM/Nekhoroshev/Partial/Bracket.lean)
LEAN_NOTE: audit N11-C PASS WITH NOTES
NOTE: -

NODE: stepN:p11:br-fast
KIND: step
TITLE: Fast part
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:br-fast@L26-L26
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:br-fast@L26-L26
CONTRACT_ID: stepN:p11:br-fast
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u,v as in Lemma bracket
SOURCE_QUANTIFIERS: u,v; rho,sigma
SOURCE_CONCLUSION: the fast part of {u,v}_c is bounded by (1/e)(1/((R_0-R+rho)sigma)+1/((s_0-s+sigma)rho))¦u¦¦v¦
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p4:bracket, bpN:p4:algebra, bpN:p4:cauchy, bpN:p11:ext-part4, bpN:p4:norm, bpN:p11:ext-class, bpN:p11:wfield
EDGE: bpN:p4:norm | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:br-fast@L26-L26 | direct package or input used by this proof step
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:br-fast@L26-L26 | direct package or input used by this proof step
EDGE: bpN:p11:wfield | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:br-fast@L26-L26 | direct package or input used by this proof step
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p4:bracket | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:br-fast@L26-L26 | the fast estimate is that of Lemma bracket (B.4), re-run for O^e
EDGE: bpN:p4:algebra | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:br-fast@L26-L26 | its proof uses algebra
EDGE: bpN:p4:cauchy | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:br-fast@L26-L26 | its proof uses cauchy
EDGE: bpN:p11:ext-part4 | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:br-fast@L26-L26 | algebra and cauchy hold for O^e with the same constants
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab+sol-review-N-f
REVIEWER: sol-delta-N-f
LEAN_STATUS: PROVED
LEAN_REF: bracket (KAM/Nekhoroshev/Partial/Bracket.lean)
LEAN_NOTE: audit N11-C PASS WITH NOTES
NOTE: the conclusion of p4:bracket is for m=n, so it is consumed through its proof (algebra, cauchy) applied to the extended class by ext-part4

NODE: stepN:p11:br-slow
KIND: step
TITLE: Slow part
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:br-slow@L27-L27
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:br-slow@L27-L27
CONTRACT_ID: stepN:p11:br-slow
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: I-hat in V_{R-rho}D-hat, t=s-sigma; u,v as in Lemma bracket
SOURCE_QUANTIFIERS: u,v; I-hat
SOURCE_CONCLUSION: the slow part: each of the 2k products d_{q_j}u d_{p_j}v, d_{p_j}u d_{q_j}v has norm <=¦u¦_{R_0,s_0}¦v¦_{R,s}/((R_0-R+rho)rho); times c and summed, 2kc/((R_0-R+rho)rho)¦u¦¦v¦
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p4:algebra, bpN:p4:cauchy, bpN:p11:ext-part4, bpN:p11:s-ext-class#data, bpN:p4:norm, bpN:p4:domains, bpN:p11:ext-class, bpN:p11:wfield
EDGE: bpN:p4:norm | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:br-slow@L27-L27 | direct use of bpN:p4:norm in the statement or proof at this span
EDGE: bpN:p4:domains | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:br-slow@L27-L27 | direct use of bpN:p4:domains in the statement or proof at this span
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:br-slow@L27-L27 | direct use of bpN:p11:ext-class in the statement or proof at this span
EDGE: bpN:p11:wfield | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:br-slow@L27-L27 | direct package or input used by this proof step
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p4:algebra | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:br-slow@L27-L27 | pointwise product estimate (Lemma algebra)
EDGE: bpN:p4:cauchy | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:br-slow@L27-L27 | Lemma cauchy(b) for the I-hat derivatives
EDGE: bpN:p11:ext-part4 | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:br-slow@L27-L27 | algebra and cauchy(b) for the extended class
EDGE: bpN:p11:s-ext-class#data | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:br-slow@L27-L27 | the weight c
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab+sol-review-N-f
REVIEWER: sol-delta-N-f
LEAN_STATUS: PROVED
LEAN_REF: bracket (KAM/Nekhoroshev/Partial/Bracket.lean)
LEAN_NOTE: audit N11-C PASS WITH NOTES
NOTE: -

NODE: stepN:p11:br-dom
KIND: step
TITLE: Domination
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:br-dom@L28-L28
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:br-dom@L28-L28
CONTRACT_ID: stepN:p11:br-dom
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (SL)_{rho,sigma}: 16 k c sigma<=rho
SOURCE_QUANTIFIERS: R_0,rho,sigma
SOURCE_CONCLUSION: 2kc/((R_0-R+rho)rho)<=(1/8)/((R_0-R+rho)sigma), and 1/e+1/8<0.493<1/2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:ext-class, bpN:p11:ext-num
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:br-dom@L28-L28 | (SL)_{rho,sigma}
EDGE: bpN:p11:ext-num | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:br-dom@L28-L28 | e>2.718 so 1/e<0.368
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab
REVIEWER: sol-review-N-f
LEAN_STATUS: PROVED
LEAN_REF: bracket_dominated (KAM/Nekhoroshev/Partial/Bracket.lean)
LEAN_NOTE: audit N11-C PASS WITH NOTES
NOTE: -

NODE: bpN:p11:bracket-g
KIND: lemma
TITLE: Bracket with a decomposed $g$
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:bracket-g@L31-L33
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:bracket-g@L34-L36
CONTRACT_ID: bpN:p11:bracket-g
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the situation of Lemma bpN:p6:bracket-g for O^e (phi in O(R,s)^e, g=sum_j g_j as in Definition p6:setting with extended norms), 0<rho<R, 0<sigma<s, (SL)_{rho,sigma}
SOURCE_QUANTIFIERS: phi; g=sum g_j; rho,sigma
SOURCE_CONCLUSION: ¦{g,phi}_c¦_{R-rho,s-sigma}<=(1/(rho sigma))¦g¦_* ¦phi¦_{R,s} (¦g¦_* as in Definition p6:setting for the extended norms)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:bracket, bpN:p6:setting, bpN:p11:ext-class, bpN:p11:wfield, bpN:p4:norm, bpN:p4:domains
EDGE: bpN:p4:norm | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:bracket-g@L34-L36 | direct use of bpN:p4:norm in the statement or proof at this span
EDGE: bpN:p4:domains | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:bracket-g@L34-L36 | direct package or input used by this proof step
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:bracket | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:bracket-g@L35-L35 | Lemma bracket applied to each g_j
EDGE: bpN:p6:setting | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:bracket-g@L32-L32 | decomposition g=sum g_j and the weighted sum ¦g¦_*
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:bracket-g@L32-L32 | O^e and (SL)_{rho,sigma}
EDGE: bpN:p11:wfield | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:bracket-g@L32-L32 | the bracket {g,phi}_c
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab+sol-review-N-f
REVIEWER: sol-delta-N-f
LEAN_STATUS: PROVED
LEAN_REF: bracket_g (KAM/Nekhoroshev/Partial/Bracket.lean)
LEAN_NOTE: audit N11-C PASS WITH NOTES
NOTE: dropped candidate edge: bpN:p6:bracket-g (only "the situation" is cited, i.e. its hypotheses; the estimate is re-derived from Lemma bracket in the proof)

NODE: bpN:p11:scaled
KIND: definition
TITLE: Scaled norm, field
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:scaled@L40-L42
PROOF_SOURCE: -
CONTRACT_ID: bpN:p11:scaled
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: R, s; 0<rho<R, 0<sigma<s; y in D^e_{R,s}
SOURCE_QUANTIFIERS: rho,sigma; a,b,xi
SOURCE_CONCLUSION: defines nu_{rho,sigma}(a,b,xi)=max(¦a¦/sigma,¦b¦/rho,¦xi¦/rho) on C^n x C^n x C^{2k}; the field X^c_phi=Omega_c grad phi with components d_I phi, -d_theta phi, c d_{p-tilde}phi, -c d_{q-tilde}phi; the closed nu-ball of radius a about y is the polydisc P-bar(y;a sigma,a rho,a rho); for a<=1 and y in D^e_{R-rho,s-sigma}: B-bar_nu(y,a) subset D^e_{R-(1-a)rho,s-(1-a)sigma}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p4:domains, bpN:p11:wfield, bpN:p11:ext-class, bpN:p11:s-ext-class#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p4:domains | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:scaled@L42-L42 | the inclusion of polydiscs is Definition p4:domains(b) for D-hat
EDGE: bpN:p11:wfield | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:scaled@L41-L41 | X^c_phi=Omega_c grad phi
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:scaled@L42-L42 | D^e_{R,s}
EDGE: bpN:p11:s-ext-class#data | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:scaled@L41-L41 | the weight c
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab
REVIEWER: sol-review-N-f
LEAN_STATUS: PROVED
LEAN_REF: scaled (KAM/Nekhoroshev/Partial/VectorField.lean)
LEAN_NOTE: audit N11-C PASS WITH NOTES
NOTE: package bpN:p11:scaled (SPEC)

NODE: bpN:p11:vf
KIND: lemma
TITLE: Size of the field
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:vf@L44-L46
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:vf@L47-L49
CONTRACT_ID: bpN:p11:vf
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: phi in O(R,s)^e of finite norm; 0<rho<R, 0<sigma<s; (SL)_{rho,sigma}
SOURCE_QUANTIFIERS: phi; rho,sigma
SOURCE_CONCLUSION: on D^e_{R-rho,s-sigma}: ¦d_{I_i}phi¦<=¦phi¦/rho, ¦d_{theta_i}phi¦<=¦phi¦/(e sigma), ¦d_{x-tilde_j}phi¦<=¦phi¦/rho and nu_{rho,sigma}(X^c_phi)<=¦phi¦_{R,s}/(rho sigma); moreover c¦phi¦/rho<=¦phi¦/(16 k sigma)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:ext-part4, bpN:p4:cauchy, bpN:p4:sup-weighted, bpN:p5:vf-bound, bpN:p11:ext-class, bpN:p11:scaled, bpN:p4:norm, bpN:p11:s-ext-class#data, bpN:p4:domains, bpN:p11:wfield
EDGE: bpN:p4:domains | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:vf@L47-L49 | direct use of bpN:p4:domains in the statement or proof at this span
EDGE: bpN:p11:wfield | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:vf@L47-L49 | direct use of bpN:p11:wfield in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:ext-part4 | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:vf@L48-L48 | B.3 and B.1(a) for the extended class (Lemma ext-part4)
EDGE: bpN:p4:cauchy | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:vf@L48-L48 | B.3 (Cauchy estimates)
EDGE: bpN:p4:sup-weighted | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:vf@L48-L48 | B.1(a)
EDGE: bpN:p5:vf-bound | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:vf@L48-L48 | the fast components as in Lemma vf-bound
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:vf@L45-L48 | (SL)_{rho,sigma}: c<=rho/(16 k sigma) gives the slow bounds
EDGE: bpN:p11:scaled | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:vf@L45-L45 | nu_{rho,sigma} and X^c_phi
EDGE: bpN:p4:norm | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:vf@L45-L45 | weighted norm
EDGE: bpN:p11:s-ext-class#data | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:vf@L48-L48 | the weight c
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab+sol-review-N-f
REVIEWER: sol-delta-N-f
LEAN_STATUS: PROVED
LEAN_REF: vf (KAM/Nekhoroshev/Partial/VectorField.lean)
LEAN_NOTE: audit N11-C PASS WITH NOTES
NOTE: -

NODE: bpN:p11:flow
KIND: lemma
TITLE: Flow package
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:flow@L51-L53
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:flow@L54-L56
CONTRACT_ID: bpN:p11:flow
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Omega=D^e_{R',s'} open; F holomorphic on Omega with nu(F)<=eps<=1/2; (d) tau=(l,0,0), l in Z^n; (e) F real on Omega cap R^{2n+2k}
SOURCE_QUANTIFIERS: F; eps; R',s'
SOURCE_CONCLUSION: Lemma bpN:p5:flow applies verbatim to N=2n+2k, the norm nu_{rho,sigma}, Omega=D^e_{R',s'}: (a)-(e), with (d) translations by (l,0,0) and (e) reality (the proof is the conjugation symmetry and does not use N=2n)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p5:flow, bpN:p11:scaled, bpN:p11:ext-class, bpN:p4:domains
EDGE: bpN:p4:domains | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:flow@L54-L56 | direct use of bpN:p4:domains in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p5:flow | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:flow@L52-L52 | Lemma flow applied verbatim (its conclusions (a)-(e)) to N=2n+2k
EDGE: bpN:p11:scaled | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:flow@L52-L52 | the norm nu_{rho,sigma}
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:flow@L52-L52 | Omega=D^e_{R',s'}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab+sol-review-N-f
REVIEWER: sol-delta-N-f
LEAN_STATUS: PROVED
LEAN_REF: ext_flow, flow_real (KAM/Nekhoroshev/Partial/Flow.lean); flow_a, flow_d (KAM/Canonical/Flow.lean); flow_b (KAM/Canonical/FlowRegular.lean); flow_c (KAM/Canonical/FlowInverse.lean)
LEAN_NOTE: audit N11-E1 PASS WITH NOTES; (a)-(d) via generic Part-5 flow_a..d on EC n k, (e) flow_real
NOTE: -

NODE: bpN:p11:symplectic
KIND: lemma
TITLE: Symplectic flow; canonical maps
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:symplectic@L58-L60
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:symplectic@L61-L63
CONTRACT_ID: bpN:p11:symplectic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the flow of Lemma flow with F=X^c_phi (phi holomorphic on Omega); Phi=X^t; u,v,H holomorphic near Phi(z)
SOURCE_QUANTIFIERS: phi; t; z; u,v,H
SOURCE_CONCLUSION: Y=DX^t(z) satisfies Y^T Omega_c^{-1} Y=Omega_c^{-1}, Y Omega_c Y^T=Omega_c, det Y=+-1; (a) {u o Phi, v o Phi}_c={u,v}_c o Phi; (b) DPhi X^c_{H o Phi}=X^c_H o Phi; (c) if y'=X^c_{H o Phi}(y) then x=Phi o y satisfies x'=X^c_H(x)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:flow, bpN:p5:flow, K:bp:p1:ext-schwarz, bpN:p11:wfield, bpN:p11:ext-chain, bpN:p11:s-ext-class#data
EDGE: bpN:p11:s-ext-class#data | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:symplectic@L61-L63 | direct use of bpN:p11:s-ext-class#data in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:flow | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:symplectic@L59-L59 | the flow package of the hypothesis
EDGE: bpN:p5:flow | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:symplectic@L62-L62 | Y'=DF Y, Y(0)=1 is Lemma flow(b)
EDGE: K:bp:p1:ext-schwarz | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:symplectic@L62-L62 | DF=Omega_c S with S the symmetric Hessian
EDGE: bpN:p11:wfield | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:symplectic@L62-L62 | Omega_c, X^c, {u,v}_c=grad u^T Omega_c grad v
EDGE: bpN:p11:ext-chain | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:symplectic@L62-L62 | chain rule for grad(u o Phi) and (b), (c)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab+sol-review-N-f
REVIEWER: sol-delta-N-f
LEAN_STATUS: PROVED
LEAN_REF: symplectic, symplectic_form, symplectic_det, symplectic_bracket, symplectic_field (KAM/Nekhoroshev/Partial/Symplectic.lean)
LEAN_NOTE: audit N11-E1 PASS WITH NOTES; (c) complex-orbit consequence follows from symplectic_field + chain rule
NOTE: -

NODE: bpN:p11:adjoint
KIND: lemma
TITLE: Iterated brackets
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:adjoint@L65-L68
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:adjoint@L69-L86
CONTRACT_ID: bpN:p11:adjoint
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: phi in O(R',s')^e, u in O(R,s)^e of finite norm; 0<rho<R, 0<sigma<s, R+rho<=R', s+sigma<=s'; (SL)_{rho,sigma}; eta=2¦phi¦_{R',s'}/(rho sigma)
SOURCE_QUANTIFIERS: phi,u; rho,sigma
SOURCE_CONCLUSION: ad^h_phi u:={ad^{h-1}_phi u,phi}_c in O(R-rho,s-sigma)^e and for h>=1: (1/h!)¦ad^h_phi u¦_{R-rho,s-sigma}<=(e^2 eta/8)^h ¦u¦_{R,s}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p11:ad-setup, stepN:p11:ad-step, stepN:p11:ad-prod, bpN:p11:ext-class, bpN:p11:wfield, bpN:p4:norm, bpN:p11:s-ext-class#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p11:ad-setup | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:adjoint@L70-L70 | proof step (setup)
EDGE: stepN:p11:ad-step | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:adjoint@L71-L71 | proof step (one step)
EDGE: stepN:p11:ad-prod | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:adjoint@L72-L85 | proof step (product)
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:adjoint@L66-L66 | O^e and (SL)_{rho,sigma}
EDGE: bpN:p11:wfield | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:adjoint@L66-L66 | ad^h_phi u defined with {.,.}_c
EDGE: bpN:p4:norm | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:adjoint@L67-L67 | weighted norm
EDGE: bpN:p11:s-ext-class#data | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:adjoint@L66-L66 | weight c
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab
REVIEWER: sol-review-N-f
LEAN_STATUS: PROVED
LEAN_REF: adjoint (KAM/Nekhoroshev/Partial/Adjoint.lean)
LEAN_NOTE: audit N11-E2 round 2 PASS WITH NOTES; full iterative estimate
NOTE: -

NODE: stepN:p11:ad-setup
KIND: step
TITLE: Setup
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:ad-setup@L70-L70
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:ad-setup@L70-L70
CONTRACT_ID: stepN:p11:ad-setup
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: phi,u,rho,sigma,h as in Lemma adjoint
SOURCE_QUANTIFIERS: h
SOURCE_CONCLUSION: with kappa=rho/h, lambda_h=sigma/h, R_i=R-i kappa, s_i=s-i lambda_h: (SL)_{kappa,lambda_h} holds (same ratio) and ad^i_phi u in O(R_i,s_i)^e by induction
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:ext-class, bpN:p4:norm, bpN:p11:wfield, bpN:p4:domains
EDGE: bpN:p4:norm | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:ad-setup@L70-L70 | direct use of bpN:p4:norm in the statement or proof at this span
EDGE: bpN:p11:wfield | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:ad-setup@L70-L70 | direct use of bpN:p11:wfield in the statement or proof at this span
EDGE: bpN:p4:domains | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:ad-setup@L70-L70 | direct package or input used by this proof step
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:ad-setup@L70-L70 | (SL)_{rho,sigma} depends only on the ratio sigma/rho
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab+sol-review-N-f
REVIEWER: sol-delta-N-f
LEAN_STATUS: PROVED
LEAN_REF: adjoint (KAM/Nekhoroshev/Partial/Adjoint.lean)
LEAN_NOTE: audit N11-E2 round 2 PASS WITH NOTES; named in handoff/audit ledger
NOTE: -

NODE: stepN:p11:ad-step
KIND: step
TITLE: One step
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:ad-step@L71-L71
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:ad-step@L71-L71
CONTRACT_ID: stepN:p11:ad-step
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:adjoint; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: i
SOURCE_CONCLUSION: ¦ad^i_phi u¦_{R_i,s_i}<=(1/2)(2/((h+i)kappa lambda_h))¦phi¦¦ad^{i-1}_phi u¦_{R_{i-1},s_{i-1}}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:bracket, bpN:p11:wfield, stepN:p11:ad-setup, bpN:p4:norm, bpN:p11:s-ext-class#data, bpN:p11:ext-class
EDGE: bpN:p4:norm | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:ad-step@L71-L71 | direct use of bpN:p4:norm in the statement or proof at this span
EDGE: bpN:p11:s-ext-class#data | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:ad-step@L71-L71 | direct use of bpN:p11:s-ext-class#data in the statement or proof at this span
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:ad-step@L71-L71 | direct package or input used by this proof step
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:bracket | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:ad-step@L71-L71 | Lemma bracket with u:=phi (radius R', width s'), v:=ad^{i-1}_phi u and losses kappa, lambda_h
EDGE: bpN:p11:wfield | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:ad-step@L71-L71 | {a,b}_c=-{b,a}_c
EDGE: stepN:p11:ad-setup | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:ad-step@L71-L71 | the radii R_i, s_i and (SL)_{kappa,lambda_h}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab+sol-review-N-f
REVIEWER: sol-delta-N-f
LEAN_STATUS: PROVED
LEAN_REF: adjoint (KAM/Nekhoroshev/Partial/Adjoint.lean)
LEAN_NOTE: audit N11-E2 round 2 PASS WITH NOTES; named in handoff/audit ledger
NOTE: -

NODE: stepN:p11:ad-prod
KIND: step
TITLE: Product
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:ad-prod@L72-L72
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:ad-prod@L72-L72
CONTRACT_ID: stepN:p11:ad-prod
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:adjoint; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: h
SOURCE_CONCLUSION: prod_{i=1}^h (h+i)=(2h)!/h! and kappa lambda_h=rho sigma/h^2 give (1/h!)¦ad^h_phi u¦<=((eta h^2/2)^h/(2h)!)¦u¦<=(e^2 eta/8)^h ¦u¦, using (2h)!>=(2h/e)^{2h}, i.e. N!>=(N/e)^N for N=2h, proved in the step from e^N=sum_{j>=0}N^j/j!>=N^N/N!
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p11:ad-step, bpN:p4:norm, bpN:p11:ext-class, bpN:p11:wfield
EDGE: bpN:p4:norm | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:ad-prod@L72-L72 | direct use of bpN:p4:norm in the statement or proof at this span
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:ad-prod@L72-L72 | direct package or input used by this proof step
EDGE: bpN:p11:wfield | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:ad-prod@L72-L72 | direct package or input used by this proof step
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p11:ad-step | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:ad-prod@L72-L72 | the recursive bound being iterated
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab+sol-review-N-f+sonnet-amend-N
REVIEWER: sol-delta-N-amend
LEAN_STATUS: PROVED
LEAN_REF: adjoint (KAM/Nekhoroshev/Partial/Adjoint.lean)
LEAN_NOTE: audit N11-E2 round 2 PASS WITH NOTES; named in handoff/audit ledger
NOTE: The factorial bound N!>=(N/e)^N is now proved inside this step (e^N=sum N^j/j!>=N^N/N!, exponential series); the earlier SOURCE_GAP is supplied.

NODE: bpN:p11:composition
KIND: theorem
TITLE: Lemma B.5 for the extended class
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:composition@L88-L93
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:composition@L94-L98
CONTRACT_ID: bpN:p11:composition
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<rho<R<=R'-rho, 0<sigma<s<=s'-sigma; phi in O(R',s')^e of finite norm; eta=2¦phi¦_{R',s'}/(rho sigma)<=1/2; (SL)_{rho,sigma}; Omega=D^e_{R'-rho,s'-sigma} supset D^e_{R,s}; nu=nu_{rho,sigma}
SOURCE_QUANTIFIERS: R,s,R',s',rho,sigma; phi; u
SOURCE_CONCLUSION: (i) nu(X^c_phi)<=eta/2<=1/4 on Omega, the flow X^t (¦t¦<=1) is defined and holomorphic on Omega^{1/2} supset D^e_{R-rho,s-sigma}, and for z in D^e_{R-rho,s-sigma}: X^t(z) in D^e_{R-(1-eta/2)rho,s-(1-eta/2)sigma} subset D^e_{R,s}; (ii) for u in O(R,s)^e of finite norm u o X^1=sum_h (1/h!) ad^h_phi u on D^e_{R-rho,s-sigma}, the series converges in the norm and ¦u o X^1¦_{R-rho,s-sigma}<=(1-eta)^{-1}¦u¦_{R,s}; (iii) the same for X^t with eta->¦t¦eta; (iv) if phi,u real on real points so is u o X^1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p11:co-field, stepN:p11:co-series, stepN:p11:co-remainder, bpN:p11:ext-class, bpN:p11:scaled, bpN:p11:adjoint, bpN:p11:wfield, bpN:p4:norm, bpN:p4:domains, bpN:p11:s-ext-class#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p11:co-field | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:composition@L95-L95 | proof step (field and domain)
EDGE: stepN:p11:co-series | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:composition@L96-L97 | proof step (series)
EDGE: stepN:p11:co-remainder | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:composition@L96-L97 | proof step (remainder)
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:composition@L89-L89 | O^e, D^e, (SL)_{rho,sigma}
EDGE: bpN:p11:scaled | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:composition@L89-L89 | nu=nu_{rho,sigma}
EDGE: bpN:p11:adjoint | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:composition@L91-L91 | ad^h_phi u in (ii)
EDGE: bpN:p11:wfield | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:composition@L90-L90 | the field X^c_phi
EDGE: bpN:p4:norm | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:composition@L89-L89 | finite weighted norm
EDGE: bpN:p4:domains | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:composition@L89-L89 | D^e_{R,s}, Omega^{1/2}
EDGE: bpN:p11:s-ext-class#data | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:composition@L89-L89 | weight c
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab
REVIEWER: sol-review-N-f
LEAN_STATUS: PROVED
LEAN_REF: composition, composition_domain, composition_real (KAM/Nekhoroshev/Partial/Composition.lean)
LEAN_NOTE: audit N11-F1-audit-1 (short-name FAIL fixed by renames; no soundness defect)
NOTE: -

NODE: stepN:p11:co-field
KIND: step
TITLE: Field and domain
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:co-field@L95-L95
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:co-field@L95-L95
CONTRACT_ID: stepN:p11:co-field
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: phi, eta, (SL)_{rho,sigma} as in Theorem composition
SOURCE_QUANTIFIERS: z
SOURCE_CONCLUSION: nu(X^c_phi)<=eta/2=:eps<=1/4 on Omega; for z in D^e_{R-rho,s-sigma}: B-bar_nu(z,1/2) subset D^e_{R-rho/2,s-sigma/2} subset D^e_{R,s} subset Omega so z in Omega^{1/2}, and X^t(z) in B-bar_nu(z,eps) subset D^e_{R-(1-eps)rho,s-(1-eps)sigma}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:vf, bpN:p11:scaled, bpN:p11:flow, bpN:p11:ext-class, bpN:p4:norm, bpN:p4:domains, bpN:p11:wfield
EDGE: bpN:p4:norm | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:co-field@L95-L95 | direct use of bpN:p4:norm in the statement or proof at this span
EDGE: bpN:p4:domains | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:co-field@L95-L95 | direct use of bpN:p4:domains in the statement or proof at this span
EDGE: bpN:p11:wfield | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:co-field@L95-L95 | direct use of bpN:p11:wfield in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:vf | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:co-field@L95-L95 | Lemma vf with losses rho, sigma gives nu(X^c_phi)<=¦phi¦/(rho sigma)
EDGE: bpN:p11:scaled | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:co-field@L95-L95 | the nu-ball inclusion of Definition scaled
EDGE: bpN:p11:flow | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:co-field@L95-L95 | Lemma flow(a): X^t(z) in B-bar_nu(z,eps)
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:co-field@L95-L95 | D^e_{R,s} and its monotone family
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab+sol-review-N-f
REVIEWER: sol-delta-N-f
LEAN_STATUS: PROVED
LEAN_REF: composition, composition_domain, composition_real (KAM/Nekhoroshev/Partial/Composition.lean)
LEAN_NOTE: audit N11-F1-audit-1 (short-name FAIL fixed by renames; no soundness defect)
NOTE: -

NODE: stepN:p11:co-series
KIND: step
TITLE: Series
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:co-series@L96-L96
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:co-series@L96-L96
CONTRACT_ID: stepN:p11:co-series
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:composition; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: u
SOURCE_CONCLUSION: (1/h!)ad^h_phi u in O(R-rho,s-sigma)^e has norm <=(e^2 eta/8)^h¦u¦, sum<=(1-e^2 eta/8)^{-1}<=(1-eta)^{-1} (e^2/8<0.93); partial sums converge uniformly (B.1(a)), the limit S is holomorphic and periodic, its Fourier coefficients are the sums of the coefficients (termwise integration), and the norm bound follows by the triangle inequality
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:adjoint, bpN:p4:sup-weighted, bpN:p11:ext-part4, bpN:p4:ext-weier, bpN:p4:ext-series, bpN:p4:norm, bpN:p4:domains, bpN:p11:ext-class, bpN:p11:ext-e-upper
EDGE: bpN:p4:domains | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:co-series@L96-L96 | direct use of bpN:p4:domains in the statement or proof at this span
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:co-series@L96-L96 | direct use of bpN:p11:ext-class in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:adjoint | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:co-series@L96-L96 | the term bounds (e^2 eta/8)^h
EDGE: bpN:p4:sup-weighted | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:co-series@L96-L96 | B.1(a): uniform convergence
EDGE: bpN:p11:ext-part4 | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:co-series@L96-L96 | B.1(a) for the extended class
EDGE: bpN:p4:ext-weier | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:co-series@L96-L96 | limit holomorphic and periodic
EDGE: bpN:p4:ext-series | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:co-series@L96-L96 | termwise integration of the Fourier coefficients
EDGE: bpN:p4:norm | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:co-series@L96-L96 | Fourier coefficients and norm of the limit
EDGE: bpN:p11:ext-e-upper | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:co-series@L96-L96 | e<2.72 gives e^2<7.4 and e^2/8<0.925<0.93 for the geometric series
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab+sol-delta-N-f+sonnet-amend-N
REVIEWER: sol-delta-N-amend
LEAN_STATUS: PROVED
LEAN_REF: composition, composition_domain, composition_real (KAM/Nekhoroshev/Partial/Composition.lean)
LEAN_NOTE: audit N11-F1-audit-1 (short-name FAIL fixed by renames; no soundness defect)
NOTE: The numerical input e^2/8<0.93 is now supplied from e<2.72 (Mathlib Real.exp_one_lt_d9), recorded as the external bpN:p11:ext-e-upper; the earlier SOURCE_GAP is dropped.

NODE: stepN:p11:co-remainder
KIND: step
TITLE: Remainder
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:co-remainder@L97-L97
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:co-remainder@L97-L97
CONTRACT_ID: stepN:p11:co-remainder
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:composition; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: N; z
SOURCE_CONCLUSION: ¦ad^N_phi u¦_{R-hat-rho,s-hat-sigma}<=N!(e^2 hat-eta/8)^N¦u¦ with e^2 hat-eta/8<0.83; Taylor with integral remainder gives ¦R_N(z)¦<=(e^2 hat-eta/8)^N¦u¦->0 so u(X^1 z)=S(z); (iii) is (ii) for t phi; (iv) by Lemma flow(e)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:adjoint, bpN:p11:flow, bpN:p11:wfield, bpN:p4:norm, bpN:p4:domains, bpN:p11:ext-class, stepN:p11:co-field, stepN:p11:co-series, bpN:p11:ext-taylor, bpN:p11:ext-e-upper, bpN:p11:ext-num
EDGE: bpN:p4:norm | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:co-remainder@L97-L97 | direct use of bpN:p4:norm in the statement or proof at this span
EDGE: bpN:p4:domains | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:co-remainder@L97-L97 | direct use of bpN:p4:domains in the statement or proof at this span
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:co-remainder@L97-L97 | direct use of bpN:p11:ext-class in the statement or proof at this span
EDGE: stepN:p11:co-field | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:co-remainder@L97-L97 | direct package or input used by this proof step
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:adjoint | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:co-remainder@L97-L97 | Lemma adjoint with (hat-rho,hat-sigma)
EDGE: bpN:p11:flow | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:co-remainder@L97-L97 | (iv) by Lemma flow(e); trajectory in D^e
EDGE: bpN:p11:wfield | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:co-remainder@L97-L97 | d/dt v(X^t z)=Dv.X^c_phi={v,phi}_c
EDGE: stepN:p11:co-series | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:co-remainder@L97-L97 | S(z) is the holomorphic series limit constructed in the preceding Series step
EDGE: bpN:p11:ext-taylor | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:co-remainder@L97-L97 | Taylor formula with integral remainder along the extended flow (Omega=D^e_{R,s}, gamma(t)=X^t(z)); Part 5 Taylor is not used
EDGE: bpN:p11:ext-e-upper | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:co-remainder@L97-L97 | e<2.72 gives e^2<7.4 and e^2/9<0.823<0.83
EDGE: bpN:p11:ext-num | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:co-remainder@L97-L97 | the upper bound e^2/9<0.83 is used together with the lower bounds of ext-num
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab+sol-global-N+sonnet-amend-N
REVIEWER: sol-delta-N-amend
LEAN_STATUS: PROVED
LEAN_REF: composition, composition_domain, composition_real (KAM/Nekhoroshev/Partial/Composition.lean)
LEAN_NOTE: audit N11-F1-audit-1 (short-name FAIL fixed by renames; no soundness defect)
NOTE: Taylor now cites the extended lemma bpN:p11:ext-taylor, not bpN:p5:taylor, and e<2.72 is supplied by bpN:p11:ext-e-upper; both earlier SOURCE_GAPs are dropped.

NODE: bpN:p11:ext-taylor
KIND: lemma
TITLE: Taylor formula along the extended flow
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:ext-taylor@L75-L81
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:ext-taylor@L82-L86
CONTRACT_ID: bpN:p11:ext-taylor
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Omega ⊂ C^{2n+2k} open; phi holomorphic on Omega; z ∈ Omega; gamma:[0,1]→Omega a C^1 curve with gamma(0)=z and gamma'(t)=X^c_phi(gamma(t)); u (and h,f_0 for the second display) holomorphic on Omega; ad^0_phi u=u, ad^j_phi u={ad^{j-1}_phi u,phi}_c (Definition bpN:p11:wfield)
SOURCE_QUANTIFIERS: n,k; Omega; phi; z; gamma; u; N>=1 (h,f_0 for the second display)
SOURCE_CONCLUSION: ad^j_phi u is holomorphic on Omega; g(t)=u(gamma(t)) is C^infty on [0,1] with g^(j)(t)=(ad^j_phi u)(gamma(t)); for every N>=1, u(gamma(1))=sum_{j<N}(1/j!)(ad^j_phi u)(z)+R_N, R_N=int_0^1 (1-t)^{N-1}/(N-1)! (ad^N_phi u)(gamma(t))dt, ¦R_N¦<=(1/N!)max_t¦(ad^N_phi u)(gamma(t))¦; and (h+f_0)(gamma(1))=h(z)+{h,phi}_c(z)+f_0(z)+int_0^1{(1-t){h,phi}_c+f_0,phi}_c(gamma(t))dt
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p11:et-one, stepN:p11:et-ind, stepN:p11:et-taylor, bpN:p11:wfield
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p11:et-one | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:ext-taylor@L83-L83 | proof step (one derivative)
EDGE: stepN:p11:et-ind | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:ext-taylor@L84-L84 | proof step (induction)
EDGE: stepN:p11:et-taylor | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:ext-taylor@L85-L85 | proof step (Taylor with integral remainder)
EDGE: bpN:p11:wfield | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:ext-taylor@L76-L76 | ad^j_phi, the bracket {,}_c and the field X^c_phi
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-amend-N
REVIEWER: sol-delta-N-amend
LEAN_STATUS: PROVED
LEAN_REF: ext_taylor_regular, ext_taylor, ext_taylor_bound, ext_taylor_second (KAM/Nekhoroshev/Partial/Lie.lean)
LEAN_NOTE: audit N11-E2 round 2 PASS WITH NOTES; first display via ext_taylor*, second display via ext_taylor_second (F1 closed)
NOTE: G4: new lemma; not an instance of Part 5 setting, so bpN:p5:taylor is not used (the \source line cites it as provenance only). Consumers: co-remainder, tr-taylor.

NODE: stepN:p11:et-one
KIND: step
TITLE: One derivative
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:et-one@L83-L83
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:et-one@L83-L83
CONTRACT_ID: stepN:p11:et-one
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:ext-taylor; v holomorphic on Omega
SOURCE_QUANTIFIERS: v
SOURCE_CONCLUSION: d/dt v(gamma(t))=Dv(gamma)·X^c_phi(gamma)={v,phi}_c(gamma(t)), continuous in t
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p1:ext-restrict, bpN:p11:wfield, K:bp:p1:holomorphic-regularity
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p1:ext-restrict | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:et-one@L83-L83 | holomorphic v is real-differentiable with derivative Dv (chain rule along the C^1 curve)
EDGE: bpN:p11:wfield | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:et-one@L83-L83 | {v,phi}_c=Dv·X^c_phi (Definition wfield)
EDGE: K:bp:p1:holomorphic-regularity | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:et-one@L83-L83 | holomorphic v and phi have continuous holomorphic first derivatives, so Dv(gamma) times X^c_phi(gamma) is continuous
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-amend-N+sol-delta-N-amend
REVIEWER: sol-delta2-N-amend
LEAN_STATUS: PROVED
LEAN_REF: ext_taylor_regular (KAM/Nekhoroshev/Partial/Lie.lean)
LEAN_NOTE: audit N11-E2 round 2 PASS WITH NOTES; chain rule (handoff/audit name et-one)
NOTE: -

NODE: stepN:p11:et-ind
KIND: step
TITLE: Induction
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:et-ind@L84-L84
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:et-ind@L84-L84
CONTRACT_ID: stepN:p11:et-ind
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:ext-taylor
SOURCE_QUANTIFIERS: j
SOURCE_CONCLUSION: ad^j_phi u is holomorphic on Omega; applying the one-derivative step to v=ad^j_phi u gives g^(j+1)=(ad^{j+1}_phi u)∘gamma, hence g in C^infty
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p11:et-one, K:bp:p1:holomorphic-regularity, bpN:p11:wfield
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p11:et-one | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:et-ind@L84-L84 | previous step applied to v=ad^j_phi u
EDGE: K:bp:p1:holomorphic-regularity | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:et-ind@L84-L84 | a bracket of holomorphic functions consists of products of first derivatives, hence holomorphic
EDGE: bpN:p11:wfield | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:et-ind@L84-L84 | definition of the bracket {,}_c and ad^j_phi
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-amend-N
REVIEWER: sol-delta-N-amend
LEAN_STATUS: PROVED
LEAN_REF: ext_taylor_regular (KAM/Nekhoroshev/Partial/Lie.lean)
LEAN_NOTE: audit N11-E2 round 2 PASS WITH NOTES; holomorphic/smooth induction
NOTE: -

NODE: stepN:p11:et-taylor
KIND: step
TITLE: Taylor
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:et-taylor@L85-L85
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:et-taylor@L85-L85
CONTRACT_ID: stepN:p11:et-taylor
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:ext-taylor; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: N>=1
SOURCE_CONCLUSION: the two displays: Taylor with integral remainder for real and imaginary parts of g at 0 evaluated at 1 and int_0^1 (1-t)^{N-1}/(N-1)! dt=1/N!; the second display is N=2 for h plus N=1 for f_0 with ad^2_phi h={{h,phi}_c,phi}_c
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p11:et-ind, K:bp:p1:ext-integral, bpN:p11:wfield
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p11:et-ind | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:et-taylor@L85-L85 | g^(j)=(ad^j_phi u)∘gamma and smoothness
EDGE: K:bp:p1:ext-integral | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:et-taylor@L85-L85 | integration by parts / integral form of the remainder, one integration by parts per order
EDGE: bpN:p11:wfield | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:et-taylor@L85-L85 | ad^2_phi h={{h,phi}_c,phi}_c and the weighted bracket in the second Taylor display
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-amend-N+sol-delta-N-amend
REVIEWER: sol-delta2-N-amend
LEAN_STATUS: PROVED
LEAN_REF: ext_taylor, ext_taylor_bound, ext_taylor_second (KAM/Nekhoroshev/Partial/Lie.lean)
LEAN_NOTE: audit N11-E2 round 2 PASS WITH NOTES; both displays proved
NOTE: -

NODE: bpN:p11:ext-e-upper
KIND: external
TITLE: Upper bound for e (inline Mathlib citation)
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:ext-e-upper@L96-L96
PROOF_SOURCE: -
CONTRACT_ID: bpN:p11:ext-e-upper
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: e<2.72 (Mathlib Real.exp_one_lt_d9), hence e^2<7.4, e^2/8<0.925<0.93 and e^2/9<0.823<0.83
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-amend-N
REVIEWER: sol-delta-N-amend
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: Cited inline in stepN:p11:co-series (L96) and stepN:p11:co-remainder (L97), not a labelled item of the External facts list and not a SPEC-listed external; recorded as an external because ext-num states only e>2.718. SPEC revision needed (writer).

NODE: bpN:p11:transform
KIND: proposition
TITLE: Lie transform with first-order remainder; integral remainders
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:transform@L100-L102
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:transform@L103-L106
CONTRACT_ID: bpN:p11:transform
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the setting of Theorem composition; h in O(R,s)^e (norm possibly infinite) with w={h,phi}_c in O(R,s)^e of finite norm; f_0 in O(R,s)^e of finite norm; v_t in O(R,s)^e (0<=t<=1) with sup_t ¦v_t¦=V<infinity and (t,z)->v_t(z),Dv_t(z) continuous
SOURCE_QUANTIFIERS: R,s,rho,sigma; phi; h; f_0; (v_t)
SOURCE_CONCLUSION: on D^e_{R-rho,s-sigma}: (h+f_0) o X^1=h+w+f_0+R with R=int_0^1{(1-t)w+f_0,phi}_c o X^t dt and ¦R¦_{R-rho,s-sigma}<=eta/(1-eta)((1/2)¦w¦+¦f_0¦); G=int_0^1 v_t o X^t dt in O(R-rho,s-sigma)^e with ¦G¦<=(1-eta)^{-1}V
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p11:tr-taylor, stepN:p11:tr-int, bpN:p11:composition, bpN:p11:ext-class, bpN:p11:wfield, bpN:p4:norm, bpN:p11:s-ext-class#data, bpN:p4:domains
EDGE: bpN:p4:domains | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:transform@L103-L106 | direct use of bpN:p4:domains in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p11:tr-taylor | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:transform@L104-L104 | proof step (Taylor)
EDGE: stepN:p11:tr-int | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:transform@L105-L105 | proof step (integral remainder)
EDGE: bpN:p11:composition | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:transform@L101-L101 | setting and the flow bounds
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:transform@L100-L101 | O^e
EDGE: bpN:p11:wfield | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:transform@L101-L101 | w={h,phi}_c
EDGE: bpN:p4:norm | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:transform@L101-L101 | finite norm
EDGE: bpN:p11:s-ext-class#data | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:transform@L101-L101 | weight c
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab+sol-delta-N-f
REVIEWER: sol-delta2-N-f
LEAN_STATUS: PROVED
LEAN_REF: transform, transform_integral (KAM/Nekhoroshev/Partial/Transform.lean)
LEAN_NOTE: audit N11-F1-audit-1 (short-name FAIL fixed by renames; no soundness defect)
NOTE: -

NODE: stepN:p11:tr-taylor
KIND: step
TITLE: Taylor
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:tr-taylor@L104-L104
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:tr-taylor@L104-L104
CONTRACT_ID: stepN:p11:tr-taylor
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:transform; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: z
SOURCE_CONCLUSION: the Taylor identity (h+f_0)(X^1 z)=h+w+f_0+R pointwise; series form: h o X^1=h+sum_{i>=0}(1/(i+1)!)ad^i_phi w, f_0 o X^1=sum(1/j!)ad^j_phi f_0, hence R=sum_{j>=1}(...) and the bound sum_{j>=1}(e^2 eta/8)^j(¦w¦/(j+1)+¦f_0¦)<=eta/(1-eta)((1/2)¦w¦+¦f_0¦)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:composition, bpN:p11:adjoint, bpN:p4:norm, bpN:p4:domains, bpN:p11:ext-class, bpN:p6:ext-numerics, bpN:p11:wfield, stepN:p11:co-remainder, bpN:p11:ext-taylor
EDGE: bpN:p4:norm | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:tr-taylor@L104-L104 | direct use of bpN:p4:norm in the statement or proof at this span
EDGE: bpN:p4:domains | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:tr-taylor@L104-L104 | direct use of bpN:p4:domains in the statement or proof at this span
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:tr-taylor@L104-L104 | direct use of bpN:p11:ext-class in the statement or proof at this span
EDGE: bpN:p6:ext-numerics | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:tr-taylor@L104-L104 | direct use of bpN:p6:ext-numerics in the statement or proof at this span
EDGE: bpN:p11:wfield | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:tr-taylor@L104-L104 | direct package or input used by this proof step
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:composition | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:tr-taylor@L104-L104 | trajectory stays in D^e_{R,s} (i)
EDGE: bpN:p11:adjoint | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:tr-taylor@L104-L104 | bounds (e^2 hat-eta/8)^{N-1} for ad^{N-1}_phi w and the series terms
EDGE: stepN:p11:co-remainder | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:tr-taylor@L104-L104 | the hatted-loss Taylor remainder estimate and its decay are reused from the composition remainder argument
EDGE: bpN:p11:ext-taylor | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:tr-taylor@L104-L104 | second display of the extended Taylor lemma (N=2 for h, N=1 for f_0; Omega=D^e_{R,s}, gamma(t)=X^t(z))
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab+sol-global-N+sonnet-amend-N
REVIEWER: sol-delta-N-amend
LEAN_STATUS: PROVED
LEAN_REF: transform, transform_integral (KAM/Nekhoroshev/Partial/Transform.lean)
LEAN_NOTE: audit N11-F1-audit-1 (short-name FAIL fixed by renames; no soundness defect)
NOTE: Taylor now cites the extended lemma bpN:p11:ext-taylor, not bpN:p5:taylor; the earlier SOURCE_GAP is dropped.

NODE: stepN:p11:tr-int
KIND: step
TITLE: Integral remainder
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:tr-int@L105-L105
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:tr-int@L105-L105
CONTRACT_ID: stepN:p11:tr-int
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: v_t as in the statement
SOURCE_QUANTIFIERS: t,z
SOURCE_CONCLUSION: g_t=v_t o X^t in O(R-rho,s-sigma)^e with ¦g_t¦<=(1-eta)^{-1}V; (t,z)->g_t(z) and D_z g_t=Dv_t(X^t z)D_z X^t(z) are continuous; G holomorphic (parameter integral) and ¦G¦_{I,s-sigma}<=int_0^1¦g_t¦_{I,s-sigma}dt by Fubini and Tonelli
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:composition, bpN:p4:ext-param, bpN:p4:ext-series, bpN:p4:norm, bpN:p11:ext-class, K:bp:p1:ext-integral, bpN:p4:domains, bpN:p11:flow
EDGE: bpN:p4:norm | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:tr-int@L105-L105 | direct use of bpN:p4:norm in the statement or proof at this span
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:tr-int@L105-L105 | direct use of bpN:p11:ext-class in the statement or proof at this span
EDGE: K:bp:p1:ext-integral | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:tr-int@L105-L105 | direct use of K:bp:p1:ext-integral in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:composition | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:tr-int@L105-L105 | (iii): ¦g_t¦<=(1-eta)^{-1}V
EDGE: bpN:p4:ext-param | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:tr-int@L105-L105 | holomorphy of G (holomorphic parameter integral)
EDGE: bpN:p4:ext-series | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:tr-int@L105-L105 | Fubini and Tonelli for the Fourier-coefficient integrals
EDGE: bpN:p4:domains | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:tr-int@L105-L105 | the integration domain D^e_{R-rho,s-sigma} is the extended instance of the Part 4 domain
EDGE: bpN:p11:flow | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:tr-int@L105-L105 | flow(b) supplies joint continuity of X^t and D_z X^t used in the parameter-integral hypothesis
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab+sol-delta-N-f
REVIEWER: sol-delta2-N-f
LEAN_STATUS: PROVED
LEAN_REF: transform, transform_integral (KAM/Nekhoroshev/Partial/Transform.lean)
LEAN_NOTE: audit N11-F1-audit-1 (short-name FAIL fixed by renames; no soundness defect)
NOTE: -

NODE: bpN:p11:canonical-map
KIND: proposition
TITLE: Canonical map package
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:canonical-map@L108-L110
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:canonical-map@L111-L113
CONTRACT_ID: bpN:p11:canonical-map
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: phi in O(R,s)^e of finite norm; 0<rho<R/2, 0<sigma<s/2; (SL)_{rho,sigma}; eps:=¦phi¦/(rho sigma)<=1/2; Omega=D^e_{R-rho,s-sigma}; Phi=X^1_phi, Psi=X^{-1}_phi
SOURCE_QUANTIFIERS: R,s,rho,sigma; phi
SOURCE_CONCLUSION: (a) Phi,Psi holomorphic on D^e_{R-3rho/2,s-3sigma/2} with values in Omega, nu(Phi-id)<=eps, ¦Phi_theta-theta¦<=¦phi¦/rho, ¦Phi_I-I¦<=¦phi¦/(e sigma), ¦Phi_{x-tilde}-x-tilde¦<=c¦phi¦/rho<=(1/(16k))¦phi¦/sigma; (b) Phi(theta+l,I,x-tilde)=Phi+(l,0,0), real points to real points if phi real; (c) ¦DPhi-1¦_nu<=2 eps on D^e_{R-2rho,s-2sigma}; (d) DPhi Omega_c DPhi^T=Omega_c; (e) Psi o Phi=id=Phi o Psi on D^e_{R-2rho,s-2sigma} and Phi maps it into D^e_{R-3rho/2,s-3sigma/2}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p5:canonical-map, bpN:p11:vf, bpN:p11:scaled, bpN:p11:flow, bpN:p11:symplectic, K:bp:p1:ext-mvt, bpN:p11:ext-class, bpN:p4:norm, bpN:p4:domains, bpN:p11:s-ext-class#data, bpN:p11:wfield
EDGE: bpN:p11:wfield | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:canonical-map@L111-L113 | direct use of bpN:p11:wfield in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p5:canonical-map | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:canonical-map@L112-L112 | as Proposition p5:canonical-map, step by step (same conclusions (a)-(e) for the extended class)
EDGE: bpN:p11:vf | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:canonical-map@L112-L112 | nu(X^c_phi)<=eps on Omega
EDGE: bpN:p11:scaled | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:canonical-map@L112-L112 | nu-ball inclusions
EDGE: bpN:p11:flow | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:canonical-map@L112-L112 | Lemma flow(a)-(e) give (a),(b),(c),(e)
EDGE: bpN:p11:symplectic | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:canonical-map@L112-L112 | (d)
EDGE: K:bp:p1:ext-mvt | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:canonical-map@L112-L112 | componentwise displacements: mean value inequality along the trajectory
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:canonical-map@L108-L109 | O^e, (SL)_{rho,sigma}, D^e
EDGE: bpN:p4:norm | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:canonical-map@L109-L109 | finite norm
EDGE: bpN:p4:domains | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:canonical-map@L109-L109 | D^e_{R-rho,s-sigma}
EDGE: bpN:p11:s-ext-class#data | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:canonical-map@L109-L109 | weight c
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab+sol-delta-N-f
REVIEWER: sol-delta2-N-f
LEAN_STATUS: PROVED
LEAN_REF: canonical_map (KAM/Nekhoroshev/Partial/CanonicalMap.lean)
LEAN_NOTE: N11-F2 audit-1 FAIL (consumer completeness only) resolved by lane-N ruling F2-C1
NOTE: the edge to bpN:p5:canonical-map is the "as ..., step by step" template whose conclusions (a)-(e) are reproved here from the extended flow, vf and symplectic lemmas

NODE: bpN:p11:hom
KIND: proposition
TITLE: Homological equation with parameters
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:hom@L119-L121
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:hom@L122-L124
CONTRACT_ID: bpN:p11:hom
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: f in O(R,s)^e, delta=¦f¦_{R,s}<infinity; Lambda subset Z^n; K_a>=0; (N-dir): ¦k.omega(I)¦>=alpha/q on V_R(I_c) for k in Z_{K_a}\Lambda; xi=P_Lambda T_{K_a}f; phi=sum_{k in Z_{K_a}\Lambda} f-hat_k(I,x-tilde)/(2 pi i k.omega(I)) chi_k(theta); for the reality clause Lambda=-Lambda, f real on real points and omega(I) real for every real I in V_R(I_c)
SOURCE_QUANTIFIERS: R,s; Lambda; K_a; alpha; q; h; f
SOURCE_CONCLUSION: xi,phi in O(R,s)^e, {phi,h}_c+xi=T_{K_a}f, ¦xi¦,¦T_{K_a}f¦<=delta, ¦phi¦<=q delta/abar, P_Lambda phi=0; under the reality hypotheses xi,phi are real on real points (false without real omega: h=iI, f=a cos 2 pi theta, Lambda={0})
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p6:homological, bpN:p6:iterative-direct, stepN:p6:hom-real, bpN:p11:ext-part4, bpN:p4:projections, bpN:p11:ext-class, bpN:p11:wfield, bpN:p11:s-nf#data, bpN:p6#data, bpN:p4:norm, bpN:p11:s-ext-class#data, bpN:p4:domains
EDGE: bpN:p4:domains | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:hom@L122-L124 | direct use of bpN:p4:domains in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p6:homological | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:hom@L123-L123 | identical to Proposition homological (Fourier coefficients at fixed I-hat; same formulas and the norm bounds q delta/abar)
EDGE: bpN:p6:iterative-direct | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:hom@L123-L123 | with Corollary iterative-direct: (N-dir) replaces (N1),(N2),K L r<=alpha/p
EDGE: stepN:p6:hom-real | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:hom@L123-L123 | reality as Step hom-real
EDGE: bpN:p11:ext-part4 | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:hom@L123-L123 | statement about Fourier coefficients in theta at fixed I-hat (Lemma ext-part4)
EDGE: bpN:p4:projections | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:hom@L120-L120 | P_Lambda, T_{K_a}
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:hom@L120-L120 | O^e, W^e real points
EDGE: bpN:p11:wfield | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:hom@L123-L123 | {phi,h}_c=d_theta phi.omega since h depends on neither theta nor x-tilde
EDGE: bpN:p11:s-nf#data | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:hom@L117-L120 | dictionary: K_a, q, abar, omega=d_I h, h on V_R(I_c)
EDGE: bpN:p6#data | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:hom@L119-L120 | Z_{K_a}, q, abar
EDGE: bpN:p4:norm | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:hom@L120-L120 | weighted norm and Fourier coefficients
EDGE: bpN:p11:s-ext-class#data | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:hom@L123-L123 | I-hat=(I,x-tilde)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab+sol-delta-N-f
REVIEWER: sol-delta2-N-f
LEAN_STATUS: PROVED
LEAN_REF: hom, homGenerator (KAM/Nekhoroshev/Partial/Homological.lean)
LEAN_NOTE: audit N11-F3 PASS WITH NOTES (all graph conclusions exported)
NOTE: dropped template: bpN:p6:setting (N1),(N2) are replaced by (N-dir) here

NODE: bpN:p11:iterative
KIND: theorem
TITLE: Iterative Lemma$^e$
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:iterative@L126-L133
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:iterative@L134-L139
CONTRACT_ID: bpN:p11:iterative
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (N-dir); s,rho,sigma>0, 2 rho<R, 2 sigma<s, (SL)_{rho,sigma}; H=h+g+f on D^e_{R,s}; g=sum_{j in J} g_j as in Definition p6:setting (extended norms); f in O(R,s)^e, delta=¦f¦_{R,s}<=abar rho sigma/(4q); phi that of Proposition hom; Phi=X^{1,c}_phi
SOURCE_QUANTIFIERS: R,s,rho,sigma; h,g,f; phi
SOURCE_CONCLUSION: (a) Phi holomorphic on D^e_{R-3rho/2,s-3sigma/2} with values in D^e_{R-rho,s-sigma}, theta-translation equivariant, symplectic (DPhi Omega_c DPhi^T=Omega_c), injective on D^e_{R-2rho,s-2sigma} (left inverse X^{-1}_phi); (b) ¦Phi_theta-theta¦<=q delta/(abar rho), ¦Phi_I-I¦<=q delta/(e abar sigma), ¦Phi_{x-tilde}-x-tilde¦<=(e/(16k))q delta/(e abar sigma); (c) H o Phi=h+g_+ +f_+ on D^e_{R-2rho,s-2sigma}, g_+=g+P_Lambda T_{K_a}f, ¦g_+-g¦<=delta; (d) ¦f_+¦_{R-2rho,s-2sigma}<=(1-2q delta/(abar rho sigma))^{-1}(q/(abar rho sigma)(¦g¦_*+delta)+e^{-2 pi K_a sigma})delta; (e) if Lambda=-Lambda and h,g,f real on real points, so are phi,g_+,f_+ and Phi preserves real points
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p11:it-gen, stepN:p11:it-map, stepN:p11:it-taylor, stepN:p11:it-est, bpN:p6:setting, bpN:p11:hom, bpN:p11:s-nf#data, bpN:p11:ext-class, bpN:p11:wfield, bpN:p4:norm, bpN:p11:s-ext-class#data, bpN:p4:domains
EDGE: bpN:p4:domains | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:iterative@L134-L139 | direct use of bpN:p4:domains in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p11:it-gen | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:iterative@L135-L135 | proof step (generating function)
EDGE: stepN:p11:it-map | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:iterative@L136-L136 | proof step ((a),(b))
EDGE: stepN:p11:it-taylor | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:iterative@L137-L137 | proof step (Taylor identity)
EDGE: stepN:p11:it-est | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:iterative@L138-L138 | proof step (estimates; (d),(e))
EDGE: bpN:p6:setting | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:iterative@L127-L127 | g=sum g_j and ¦g¦_* of Definition p6:setting
EDGE: bpN:p11:hom | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:iterative@L127-L127 | phi of Proposition hom
EDGE: bpN:p11:s-nf#data | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:iterative@L126-L127 | h on V_R(I_c), omega, K_a, q, abar
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:iterative@L126-L127 | O^e, (SL)_{rho,sigma}
EDGE: bpN:p11:wfield | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:iterative@L127-L127 | Phi=X^{1,c}_phi
EDGE: bpN:p4:norm | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:iterative@L127-L127 | weighted norm
EDGE: bpN:p11:s-ext-class#data | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:iterative@L127-L127 | weight c
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab+sol-delta-N-f
REVIEWER: sol-delta2-N-f
LEAN_STATUS: PROVED
LEAN_REF: iterative (KAM/Nekhoroshev/Partial/Iterative.lean); helpers in IterativeMap.lean, IterativeRemainder.lean
LEAN_NOTE: audit N11-H-audit-1 PASS WITH NOTES; signature amended by ruling F2-C1 (hc : 0 < b.c); retro delta audit N11-F2-audit-2 PASS WITH NOTES (F2-C1 resolved by hc premise)
NOTE: -

NODE: stepN:p11:it-gen
KIND: step
TITLE: Generating function
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:it-gen@L135-L135
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:it-gen@L135-L135
CONTRACT_ID: stepN:p11:it-gen
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:iterative; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: f
SOURCE_CONCLUSION: ¦phi¦<=q delta/abar and eta:=2¦phi¦/(rho sigma)<=2 q delta/(abar rho sigma)<=1/2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:hom, bpN:p4:norm, bpN:p11:s-nf#data
EDGE: bpN:p4:norm | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:it-gen@L135-L135 | direct use of bpN:p4:norm in the statement or proof at this span
EDGE: bpN:p11:s-nf#data | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:it-gen@L135-L135 | direct use of bpN:p11:s-nf#data in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:hom | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:it-gen@L135-L135 | ¦phi¦<=q delta/abar
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab+sol-review-N-f
REVIEWER: sol-delta-N-f
LEAN_STATUS: PROVED
LEAN_REF: iterative (KAM/Nekhoroshev/Partial/Iterative.lean); helpers in IterativeMap.lean, IterativeRemainder.lean
LEAN_NOTE: audit N11-H-audit-1 PASS WITH NOTES; signature amended by ruling F2-C1 (hc : 0 < b.c)
NOTE: -

NODE: stepN:p11:it-map
KIND: step
TITLE: (a), (b)
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:it-map@L136-L136
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:it-map@L136-L136
CONTRACT_ID: stepN:p11:it-map
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:iterative; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: phi
SOURCE_CONCLUSION: (a),(b): eps=¦phi¦/(rho sigma)<=eta/2<=1/4 and rho<R/2, sigma<s/2 so Proposition canonical-map gives the map properties and displacement bounds
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:canonical-map, stepN:p11:it-gen, bpN:p4:norm
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:canonical-map | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:it-map@L136-L136 | Proposition canonical-map applies (rho<R/2, sigma<s/2, eps<=1/4)
EDGE: stepN:p11:it-gen | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:it-map@L136-L136 | eta<=1/2 and ¦phi¦<=q delta/abar
EDGE: bpN:p4:norm | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:it-map@L136-L136 | epsilon=¦phi¦/(rho sigma) is the weighted-norm quantity in the canonical-map hypotheses
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab+sol-delta-N-f
REVIEWER: sol-delta2-N-f
LEAN_STATUS: PROVED
LEAN_REF: iterative (KAM/Nekhoroshev/Partial/Iterative.lean); helpers in IterativeMap.lean, IterativeRemainder.lean
LEAN_NOTE: audit N11-H-audit-1 PASS WITH NOTES; signature amended by ruling F2-C1 (hc : 0 < b.c)
NOTE: -

NODE: stepN:p11:it-taylor
KIND: step
TITLE: Taylor identity
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:it-taylor@L137-L137
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:it-taylor@L137-L137
CONTRACT_ID: stepN:p11:it-taylor
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:iterative; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: phi
SOURCE_CONCLUSION: on D^e_{R-2rho,s-2sigma}: (h+f_0) o Phi=h+g+xi+R=h+g_+ +R, R=int_0^1{g+f_t,phi}_c o X^t dt, f_t=(1-t)xi+t T_{K_a}f; hence H o Phi=h+g_+ +f_+ with f_+=R+(f-T_{K_a}f) o Phi
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:transform, bpN:p11:hom, stepN:p11:it-gen, bpN:p4:norm, bpN:p4:domains, bpN:p11:ext-class, bpN:p11:wfield, bpN:p11:s-ext-class#data, bpN:p11:s-nf#data, bpN:p4:projections, bpN:p6:setting
EDGE: bpN:p4:norm | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:it-taylor@L137-L137 | direct use of bpN:p4:norm in the statement or proof at this span
EDGE: bpN:p4:domains | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:it-taylor@L137-L137 | direct use of bpN:p4:domains in the statement or proof at this span
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:it-taylor@L137-L137 | direct use of bpN:p11:ext-class in the statement or proof at this span
EDGE: bpN:p11:wfield | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:it-taylor@L137-L137 | direct use of bpN:p11:wfield in the statement or proof at this span
EDGE: bpN:p11:s-ext-class#data | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:it-taylor@L137-L137 | direct use of bpN:p11:s-ext-class#data in the statement or proof at this span
EDGE: bpN:p11:s-nf#data | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:it-taylor@L137-L137 | direct use of bpN:p11:s-nf#data in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:transform | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:it-taylor@L137-L137 | Proposition transform with data (R-rho,s-sigma;R,s)
EDGE: bpN:p11:hom | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:it-taylor@L137-L137 | w={h,phi}_c=xi-T_{K_a}f and xi=P_Lambda T_{K_a}f
EDGE: stepN:p11:it-gen | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:it-taylor@L137-L137 | eta<=1/2, the hypotheses of the transform
EDGE: bpN:p4:projections | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:it-taylor@L137-L137 | f_0=g+T_{K_a}f and f-T_{K_a}f use the Fourier truncation operator
EDGE: bpN:p6:setting | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:it-taylor@L137-L137 | the finite decomposition g=sum_j g_j supplies the stated finite-norm bound for f_0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab+sol-delta-N-f
REVIEWER: sol-delta2-N-f
LEAN_STATUS: PROVED
LEAN_REF: iterative (KAM/Nekhoroshev/Partial/Iterative.lean); helpers in IterativeMap.lean, IterativeRemainder.lean
LEAN_NOTE: audit N11-H-audit-1 PASS WITH NOTES; signature amended by ruling F2-C1 (hc : 0 < b.c)
NOTE: -

NODE: stepN:p11:it-est
KIND: step
TITLE: Estimates
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:it-est@L138-L138
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:it-est@L138-L138
CONTRACT_ID: stepN:p11:it-est
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:iterative; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: t
SOURCE_CONCLUSION: ¦v_t¦_{R-rho,s-sigma}<=(1/(rho sigma))(¦g¦_*+delta)q delta/abar=V; ¦R¦<=(1-eta)^{-1}V; ¦f-T_{K_a}f¦_{R,s-sigma}<=e^{-2 pi K_a sigma}delta and ¦(f-T_{K_a}f) o Phi¦<=(1-eta)^{-1}e^{-2 pi K_a sigma}delta; this is (d); (e) as Step it-real
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:bracket-g, bpN:p11:transform, bpN:p4:projections, bpN:p11:composition, stepN:p6:it-real, stepN:p11:it-taylor, stepN:p11:it-gen, bpN:p4:norm, bpN:p11:wfield, bpN:p11:s-nf#data, bpN:p6:setting, bpN:p11:ext-class, bpN:p11:ext-part4
EDGE: bpN:p4:norm | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:it-est@L138-L138 | direct use of bpN:p4:norm in the statement or proof at this span
EDGE: bpN:p11:wfield | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:it-est@L138-L138 | direct use of bpN:p11:wfield in the statement or proof at this span
EDGE: bpN:p11:s-nf#data | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:it-est@L138-L138 | direct use of bpN:p11:s-nf#data in the statement or proof at this span
EDGE: bpN:p6:setting | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:it-est@L138-L138 | direct use of bpN:p6:setting in the statement or proof at this span
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:it-est@L138-L138 | direct package or input used by this proof step
EDGE: bpN:p11:ext-part4 | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:it-est@L138-L138 | direct package or input used by this proof step
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:bracket-g | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:it-est@L138-L138 | decomposition g_j plus the term f_t with weight 1
EDGE: bpN:p11:transform | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:it-est@L138-L138 | ¦R¦<=(1-eta)^{-1}V
EDGE: bpN:p4:projections | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:it-est@L138-L138 | ¦f-T_{K_a}f¦_{R,s-sigma}<=e^{-2 pi K_a sigma}delta
EDGE: bpN:p11:composition | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:it-est@L138-L138 | (ii) for (f-T_{K_a}f) o Phi
EDGE: stepN:p6:it-real | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:it-est@L138-L138 | (e) as Step it-real
EDGE: stepN:p11:it-taylor | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:it-est@L138-L138 | the identity for f_+ and f_t
EDGE: stepN:p11:it-gen | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:it-est@L138-L138 | ¦phi¦<=q delta/abar and eta
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab+sol-review-N-f
REVIEWER: sol-delta-N-f
LEAN_STATUS: PROVED
LEAN_REF: iterative (KAM/Nekhoroshev/Partial/Iterative.lean); helpers in IterativeMap.lean, IterativeRemainder.lean
LEAN_NOTE: audit N11-H-audit-1 PASS WITH NOTES; signature amended by ruling F2-C1 (hc : 0 < b.c)
NOTE: the reality clause (e) is delegated to the Part 6 step it-real by "as"; modelled as an edge to that step

NODE: bpN:p11:nf
KIND: theorem
TITLE: Normal Form Lemma$^e$
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:nf@L141-L147
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:nf@L148-L160
CONTRACT_ID: bpN:p11:nf
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K_a>0; Lambda=-Lambda subset Z^n; h holomorphic on V_R(I_c) and real on real points; ({I_c},R,K_a,alpha,L,Lambda,h) satisfy (N1),(N2) (cond-nr, cond-L) and K_a L R<=alpha/p (so (N-dir), Lemma divisor); R=r_B; s>0; (SL): c<=R/(32 k s); f in O(R,s)^{e,R} (real on real points) with ¦f¦_{R,s}<=eps for a number eps>0; H=h+f; (i) eps<=alpha R/(2^7 q K_a), (ii) kappa=2 pi K_a s>=6
SOURCE_QUANTIFIERS: R,s; K_a,alpha,L,Lambda,p; h; f; eps
SOURCE_CONCLUSION: with R_*=R/2, s_*=s/6, c_1=2 q K_a/(alpha R), g_0=P_Lambda T_{K_a}f: there are a holomorphic injective Psi: D^e_{R_*,s_*}->D^e_{R,s} with DPsi Omega_c DPsi^T=Omega_c, Psi(theta+l,I,x-tilde)=Psi+(l,0,0), real at real points, and g,f_* in O(R_*,s_*)^{e,R}, g a trigonometric polynomial in theta with frequencies in Lambda cap Z_{K_a}, with H o Psi=h+g+f_* and (a) ¦g-g_0¦<=16 c_1 eps^2; (b) ¦f_*¦<=e^{-kappa/6}eps; (c) ¦Pi_I Psi-I¦<=q K_a eps/alpha<=R/2^7, ¦Pi_theta Psi-theta¦<=10 q eps/(2 pi alpha R), ¦Pi_{x-tilde}Psi-x-tilde¦<=(1/8)q K_a eps/alpha<=R/2^10 (physical slow displacement <=w/2^10)
CONSTANT_SCOPE: q=p/(p-1); R_*=R/2, s_*=s/6, c_1=2qK_a/(alpha R); the constants in (a)-(c) are absolute (as in Theorem p6:normal-form)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p11:nf-sl, stepN:p11:nf-first, stepN:p11:nf-case, stepN:p11:nf-N, stepN:p11:nf-induct, stepN:p11:nf-concl, stepN:p11:nf-disp, stepN:p11:nf-real, bpN:p6:setting, bpN:p6:divisor, bpN:p6:normal-form, bpN:p11:iterative, bpN:p11:s-nf#data, bpN:p11:s-ext-class#data, bpN:p11:ext-class, bpN:p4:projections, bpN:p6#data, bpN:p4:norm, bpN:p4:domains, bpN:p11:wfield
EDGE: bpN:p4:domains | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:nf@L148-L160 | direct use of bpN:p4:domains in the statement or proof at this span
EDGE: bpN:p11:wfield | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:nf@L148-L160 | direct use of bpN:p11:wfield in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p11:nf-sl | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:nf@L150-L150 | proof step ((SL) at every step)
EDGE: stepN:p11:nf-first | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:nf@L151-L151 | proof step (step 0 hypotheses)
EDGE: stepN:p11:nf-case | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:nf@L152-L154 | proof step (step 0, two cases)
EDGE: stepN:p11:nf-N | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:nf@L155-L155 | proof step (number of steps)
EDGE: stepN:p11:nf-induct | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:nf@L156-L156 | proof step (induction)
EDGE: stepN:p11:nf-concl | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:nf@L157-L157 | proof step (conclusion)
EDGE: stepN:p11:nf-disp | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:nf@L158-L158 | proof step (displacement)
EDGE: stepN:p11:nf-real | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:nf@L159-L159 | proof step (reality)
EDGE: bpN:p6:setting | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:nf@L142-L142 | hypotheses (N1),(N2) (cond-nr, cond-L) and the decomposition norm
EDGE: bpN:p6:divisor | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:nf@L142-L142 | K_a L R<=alpha/p gives (N-dir) by Lemma divisor
EDGE: bpN:p6:normal-form | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:nf@L149-L149 | indexing and step structure of Theorem normal-form (as there)
EDGE: bpN:p11:iterative | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:nf@L149-L149 | step i is Theorem iterative
EDGE: bpN:p11:s-nf#data | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:nf@L142-L142 | dictionary: K_a, q, abar, kappa, omega, h on V_R(I_c)
EDGE: bpN:p11:s-ext-class#data | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:nf@L142-L142 | R=r_B, c, lambda, x-tilde
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:nf@L142-L145 | O^e, (SL), D^e, Omega_c
EDGE: bpN:p4:projections | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:nf@L144-L144 | g_0=P_Lambda T_{K_a}f
EDGE: bpN:p6#data | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:nf@L143-L143 | kappa=2 pi K_a s, Z_{K_a}
EDGE: bpN:p4:norm | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:nf@L142-L142 | weighted norm
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab+sol-review-N-f
REVIEWER: sol-delta-N-f
LEAN_STATUS: PROVED
LEAN_REF: nf (KAM/Nekhoroshev/Partial/NormalForm.lean)
LEAN_NOTE: audit N11-K-audit-1 PASS WITH NOTES; (c) radius tails qKε/α ≤ R/2^7, (1/8)qKε/α ≤ R/2^10, w/2^10: nnf_disp_radius
NOTE: source: Pos93 pp.192-196 and Theorem p6:normal-form; the slow displacement (c) is new. The edge to bpN:p6:normal-form is the structural "indexing as in" template (the proof re-derives every estimate; only the theta-displacement is taken from Part 6, see nf-disp)

NODE: stepN:p11:nf-sl
KIND: step
TITLE: (SL) at every step
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-sl@L150-L150
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-sl@L150-L150
CONTRACT_ID: stepN:p11:nf-sl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (SL): c<=R/(32 k s); the losses (rho_0,sigma_0)=(R/8,s/6), (rho',sigma')=(R/4,s/3), (rho,sigma)=(R/(8N),s/(4N))
SOURCE_QUANTIFIERS: step i
SOURCE_CONCLUSION: sigma/rho in {4s/(3R),4s/(3R),2s/R} so sigma<=2 s rho/R and (SL) gives 16 k c sigma<=R sigma/(2s)<=rho, i.e. (SL)_{rho,sigma} at every step
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:ext-class
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-sl@L150-L150 | (SL) implies (SL)_{rho,sigma} whenever sigma<=2 s rho/r_B
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab
REVIEWER: sol-review-N-f
LEAN_STATUS: PROVED
LEAN_REF: nf (KAM/Nekhoroshev/Partial/NormalForm.lean)
LEAN_NOTE: audit N11-K-audit-1 PASS WITH NOTES; induction in NormalFormInduction.lean
NOTE: -

NODE: stepN:p11:nf-first
KIND: step
TITLE: Step 0: hypotheses
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-first@L151-L151
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-first@L151-L151
CONTRACT_ID: stepN:p11:nf-first
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:nf; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: eps
SOURCE_CONCLUSION: eps<=alpha R/(2^7 q K_a)<=abar rho_0 sigma_0/(16 q) so y_0:=q eps/(abar rho_0 sigma_0)<=1/16 and the hypothesis delta<=abar rho sigma/(4q) of Theorem iterative holds
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:s-nf#data
EDGE: bpN:p11:s-nf#data | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-first@L151-L151 | direct use of bpN:p11:s-nf#data in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab+sol-delta-N-f
REVIEWER: sol-delta2-N-f
LEAN_STATUS: PROVED
LEAN_REF: nf (KAM/Nekhoroshev/Partial/NormalForm.lean)
LEAN_NOTE: audit N11-K-audit-1 PASS WITH NOTES; induction in NormalFormInduction.lean
NOTE: -

NODE: stepN:p11:nf-case
KIND: step
TITLE: Step 0: two cases
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-case@L152-L154
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-case@L152-L154
CONTRACT_ID: stepN:p11:nf-case
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:nf; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: eps
SOURCE_CONCLUSION: Theorem iterative(d) with g=0: ¦f_1¦<=(1-2y_0)^{-1}(y_0+e^{-kappa/6})eps; Case A (e^{-kappa/6}<=y_0): eps_1<=(16/7)y_0 eps<=eps/kappa<=eps/4 (6.1); Case B: repeat with losses (R/4,s/3): ¦f_1¦_{R/2,s/3}<0.64 e^{-kappa/6}eps; stop with Psi=Phi_0', g=g_0, f_*=f_1 so (a),(b) hold
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:iterative, stepN:p11:nf-first, bpN:p6:ext-numerics, bpN:p11:ext-num, bpN:p4:norm, bpN:p4:domains, bpN:p11:ext-class, bpN:p11:s-nf#data, stepN:p11:nf-sl, bpN:p6:divisor
EDGE: bpN:p4:norm | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-case@L152-L154 | direct use of bpN:p4:norm in the statement or proof at this span
EDGE: bpN:p4:domains | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-case@L152-L154 | direct use of bpN:p4:domains in the statement or proof at this span
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-case@L152-L154 | direct use of bpN:p11:ext-class in the statement or proof at this span
EDGE: bpN:p11:s-nf#data | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-case@L152-L154 | direct use of bpN:p11:s-nf#data in the statement or proof at this span
EDGE: stepN:p11:nf-sl | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-case@L152-L154 | direct use of stepN:p11:nf-sl in the statement or proof at this span
EDGE: bpN:p6:divisor | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-case@L152-L154 | direct use of bpN:p6:divisor in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:iterative | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-case@L152-L152 | Theorem iterative(d) with g=0
EDGE: stepN:p11:nf-first | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-case@L152-L152 | y_0<=1/16 and the hypotheses of step 0
EDGE: bpN:p6:ext-numerics | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-case@L152-L152 | (1-2y_0)^{-1}<=8/7 etc. (numerics of Part 6)
EDGE: bpN:p11:ext-num | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-case@L154-L154 | e>2.718 so 1/e<0.368
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab+sol-review-N-f
REVIEWER: sol-delta-N-f
LEAN_STATUS: PROVED
LEAN_REF: nf (KAM/Nekhoroshev/Partial/NormalForm.lean)
LEAN_NOTE: audit N11-K-audit-1 PASS WITH NOTES; Case B proves |f_1| ≤ (32/31)(3/4)e^(-κ/6)ε (≈0.774, not 0.64), enough for (b)
NOTE: forward pointer to Step nf-disp dropped. This step is where the extended bracket constant 1 (instead of 2/e) is checked (Remark deviations)

NODE: stepN:p11:nf-N
KIND: step
TITLE: Number of steps
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-N@L155-L155
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-N@L155-L155
CONTRACT_ID: stepN:p11:nf-N
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:nf; inside Case A, splitting N=0 and N>=1; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: N
SOURCE_CONCLUSION: N=floor(kappa/(12 ln 2)), kappa>8N; N=0: Psi=Phi_0, g=g_0, f_*=f_1, ¦f_*¦<=eps/4<=e^{-kappa/6}eps; N>=1: rho=R/(8N), sigma=s/(4N), R_i=3R/4-2(i-1)rho, s_i=2s/3-2(i-1)sigma, R_{N+1}=R_*, s_{N+1}=s_*, e^{-2 pi K_a sigma}<=1/8, rho sigma=Rs/(32N^2), eps<=abar R s/(2^10 q N), hence by (6.1) eps_1<=abar rho sigma/(2^8 q) (6.2)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p11:nf-case, bpN:p6:ext-numerics, bpN:p4:norm, bpN:p11:s-nf#data
EDGE: bpN:p4:norm | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-N@L155-L155 | direct use of bpN:p4:norm in the statement or proof at this span
EDGE: bpN:p11:s-nf#data | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-N@L155-L155 | direct use of bpN:p11:s-nf#data in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p11:nf-case | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-N@L155-L155 | (6.1) eps_1<=eps/4 and eps_1<=2^7 q eps^2/(abar R s)
EDGE: bpN:p6:ext-numerics | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-N@L155-L155 | 12 ln 2>8, ln 2>2/3, e^{-3 ln 2}=1/8
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab+sol-review-N-f
REVIEWER: sol-delta-N-f
LEAN_STATUS: PROVED
LEAN_REF: nf (KAM/Nekhoroshev/Partial/NormalForm.lean)
LEAN_NOTE: audit N11-K-audit-1 PASS WITH NOTES; N = ⌊κ/(12 ln 2)⌋ with 8N ≤ κ (non-strict), R/2 ≤ R_(N+1)
NOTE: -

NODE: stepN:p11:nf-induct
KIND: step
TITLE: Induction
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-induct@L156-L156
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-induct@L156-L156
CONTRACT_ID: stepN:p11:nf-induct
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:nf; inside Case A with N>=1, using the usual induction hypothesis at step i; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: i in 1..N
SOURCE_CONCLUSION: step i is admissible and eps_{i+1}<=eps_i/4 (<0.1930 eps_i), so eps_i<=4^{1-i}eps_1; ¦g_{i-1}¦_*<=abar rho sigma/(2^4 q) with weights <=1/2 for g_j-g_{j-1} on V_j (j>=1) and <=1/N for g_0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:iterative, stepN:p11:nf-N, stepN:p11:nf-case, stepN:p11:nf-sl, bpN:p6:setting, bpN:p6:ext-numerics, bpN:p4:domains, bpN:p11:s-nf#data, bpN:p4:norm, bpN:p11:ext-class
EDGE: bpN:p4:domains | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-induct@L156-L156 | direct use of bpN:p4:domains in the statement or proof at this span
EDGE: bpN:p11:s-nf#data | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-induct@L156-L156 | direct use of bpN:p11:s-nf#data in the statement or proof at this span
EDGE: bpN:p4:norm | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-induct@L156-L156 | direct package or input used by this proof step
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-induct@L156-L156 | direct package or input used by this proof step
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:iterative | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-induct@L156-L156 | Theorem iterative(d) at step i
EDGE: stepN:p11:nf-N | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-induct@L156-L156 | the radii R_i,s_i, (6.2), e^{-2 pi K_a sigma}<=1/8
EDGE: stepN:p11:nf-case | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-induct@L156-L156 | eps_1 bound and eps<=...
EDGE: stepN:p11:nf-sl | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-induct@L156-L156 | (SL)_{rho,sigma} at every step
EDGE: bpN:p6:setting | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-induct@L156-L156 | ¦g_{i-1}¦_* computed from the decomposition with its weights
EDGE: bpN:p6:ext-numerics | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-induct@L156-L156 | (1-2^{-7})^{-1}=128/127 and 4^{1-i} sums
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab+sol-review-N-f
REVIEWER: sol-delta-N-f
LEAN_STATUS: PROVED
LEAN_REF: nf (KAM/Nekhoroshev/Partial/NormalForm.lean)
LEAN_NOTE: audit N11-K-audit-1 PASS WITH NOTES; induction on i in nnf_inv_all; weights ≤ 1 (not 1/2) for j ≥ 1, enough for u ≤ 2^-4
NOTE: -

NODE: stepN:p11:nf-concl
KIND: step
TITLE: Conclusion
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-concl@L157-L157
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-concl@L157-L157
CONTRACT_ID: stepN:p11:nf-concl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:nf; inside Case A with N>=1 after the stopping cases at L141-L142; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: N
SOURCE_CONCLUSION: H o Psi=h+g+f_*, holomorphy, symplecticity (D Phi_i Omega_c D Phi_i^T=Omega_c), periodicity, injectivity from the telescoping lemma; (b) eps_{N+1}<=4^{-N-1}eps<=e^{-kappa/6}eps; (a) ¦g-g_0¦<=(4/3)eps_1<=16 c_1 eps^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p6:telescope, bpN:p11:iterative, stepN:p11:nf-induct, stepN:p11:nf-N, stepN:p11:nf-case, bpN:p4:norm, bpN:p4:domains, bpN:p11:ext-class, bpN:p11:wfield, bpN:p11:s-nf#data, bpN:p6:ext-numerics
EDGE: bpN:p4:norm | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-concl@L157-L157 | direct use of bpN:p4:norm in the statement or proof at this span
EDGE: bpN:p4:domains | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-concl@L157-L157 | direct use of bpN:p4:domains in the statement or proof at this span
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-concl@L157-L157 | direct use of bpN:p11:ext-class in the statement or proof at this span
EDGE: bpN:p11:wfield | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-concl@L157-L157 | direct use of bpN:p11:wfield in the statement or proof at this span
EDGE: bpN:p11:s-nf#data | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-concl@L157-L157 | direct use of bpN:p11:s-nf#data in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p6:telescope | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-concl@L157-L157 | Lemma telescope for subsets of C^{2n+2k} and maps with D Phi_i Omega_c D Phi_i^T=Omega_c
EDGE: bpN:p11:iterative | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-concl@L157-L157 | H_{i+1}=H_i o Phi_i and the properties of each Phi_i from Theorem iterative
EDGE: stepN:p11:nf-induct | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-concl@L157-L157 | eps_i<=4^{1-i}eps_1
EDGE: stepN:p11:nf-N | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-concl@L157-L157 | N, kappa>8, N+1>kappa/(12 ln 2)
EDGE: stepN:p11:nf-case | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-concl@L157-L157 | eps_1<=2^7 q eps^2/(abar R s)
EDGE: bpN:p6:ext-numerics | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-concl@L157-L157 | sum of the geometric increment bounds gives the printed factor 4/3
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab+sol-delta-N-f
REVIEWER: sol-delta2-N-f
LEAN_STATUS: PROVED
LEAN_REF: nf (KAM/Nekhoroshev/Partial/NormalForm.lean)
LEAN_NOTE: audit N11-K-audit-1 PASS WITH NOTES; induction in NormalFormInduction.lean
NOTE: SOURCE_GAP: Part 11b L144-L145 asserts the extended telescoping application. Part 6 telescope is stated on C^{2n} with (DPhi)^T J DPhi=J, not for the arbitrary constant form Omega_c in the extended space. Its proof is a template; the required extension (and, at L144, translation equivariance under composition) is not stated there. No additional symplectic premise is imposed on nf.

NODE: stepN:p11:nf-disp
KIND: step
TITLE: Displacement
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-disp@L158-L158
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-disp@L158-L158
CONTRACT_ID: stepN:p11:nf-disp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:nf; handle Case A and Case B separately (not their conjunction); prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: i
SOURCE_CONCLUSION: by telescoping with the seminorms Pi_I, Pi_theta, Pi_{x-tilde}: Case A ¦Pi_I Psi-I¦<=1.17 q K_a eps/(e alpha)<=q K_a eps/alpha, ¦Pi_theta Psi-theta¦<=10 q eps/(abar R), ¦Pi_{x-tilde}Psi-x-tilde¦<=(e/16)1.17 q K_a eps/(e alpha)<(1/8)q K_a eps/alpha<=R/2^10 (by (i)); Case B: half of these
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p6:telescope, bpN:p11:iterative, stepN:p11:nf-case, stepN:p11:nf-N, stepN:p11:nf-induct, stepN:p6:nf-disp, bpN:p11:ext-num, bpN:p6:ext-numerics, bpN:p11:s-nf#data
EDGE: bpN:p11:s-nf#data | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-disp@L158-L158 | direct use of bpN:p11:s-nf#data in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p6:telescope | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-disp@L158-L158 | Lemma telescope with the seminorms
EDGE: bpN:p11:iterative | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-disp@L158-L158 | Theorem iterative(b) per step
EDGE: stepN:p11:nf-case | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-disp@L158-L158 | Case A/B parameters, eps_1<=eps/4
EDGE: stepN:p11:nf-N | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-disp@L158-L158 | sigma=s/(4N), N, kappa
EDGE: stepN:p11:nf-induct | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-disp@L158-L158 | eps_i<=4^{1-i}eps_1
EDGE: stepN:p6:nf-disp | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-disp@L158-L158 | theta-displacement bound as in Part 6
EDGE: bpN:p11:ext-num | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-disp@L158-L158 | e>2.718 for the constants 1.17 and (e/16)
EDGE: bpN:p6:ext-numerics | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-disp@L158-L158 | 12 ln 2>8
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab+sol-review-N-f
REVIEWER: sol-delta-N-f
LEAN_STATUS: PROVED
LEAN_REF: nf (KAM/Nekhoroshev/Partial/NormalForm.lean)
LEAN_NOTE: audit N11-K-audit-1 PASS WITH NOTES; Case B proves the Case A bounds (not half); R/2^10 tail: nnf_disp_radius
NOTE: SOURCE_GAP: Part 11b L144-L145 asserts the extended telescoping application. Part 6 telescope is stated on C^{2n} with (DPhi)^T J DPhi=J, not for the arbitrary constant form Omega_c in the extended space. Its proof is a template; the required extension (and, at L144, translation equivariance under composition) is not stated there. No additional symplectic premise is imposed on nf.

NODE: stepN:p11:nf-real
KIND: step
TITLE: Reality
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-real@L159-L159
PROOF_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-real@L159-L159
CONTRACT_ID: stepN:p11:nf-real
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:nf; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: i
SOURCE_CONCLUSION: Psi is real at real points and g,f_* real
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:iterative
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:iterative | blueprint-N/parts/p11b-partial-nf.tex#stepN:p11:nf-real@L159-L159 | Theorem iterative(e) at each step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab+sol-review-N-f
REVIEWER: sol-delta-N-f
LEAN_STATUS: PROVED
LEAN_REF: nf (KAM/Nekhoroshev/Partial/NormalForm.lean)
LEAN_NOTE: audit N11-K-audit-1 PASS WITH NOTES; induction in NormalFormInduction.lean
NOTE: -

NODE: bpN:p11:s-ext-class#data
KIND: definition
TITLE: Data of the extended class: I_c, S, r_B, w, lambda, c, x-tilde
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:s-ext-class#data@L4-L6
PROOF_SOURCE: -
CONTRACT_ID: bpN:p11:s-ext-class#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n>=1, k>=1; I_c in R^n a fixed base action; S subset R^{2k} a fixed set of physical slow pairs x=(q,p); a starting radius r_B>0 and a physical slow width w>0
SOURCE_QUANTIFIERS: n,k; I_c; S; r_B; w
SOURCE_CONCLUSION: defines lambda:=w/r_B, c:=2 pi/lambda^2=2 pi r_B^2/w^2, x-tilde:=x/lambda, S-tilde:=lambda^{-1}S; lambda and c are never recomputed during an iteration (an iterated radius R<=r_B has physical slow tube width lambda R)
CONSTANT_SCOPE: lambda, c fixed once and for all by (r_B,w); later S=core(D,3d/4)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab
REVIEWER: sol-review-N-f
LEAN_STATUS: PROVED
LEAN_REF: PartialBlock, PartialBlock.lam, PartialBlock.c, PartialBlock.base (KAM/Nekhoroshev/Partial/Setting.lean)
LEAN_NOTE: audit N11-A PASS WITH NOTES; x-tilde and S-tilde inlined in base, not separate defs
NOTE: section-data node for coverage item p11b:prose-L4-L6 (SPEC table); used by symbol in ext-class, bracket, scaled, vf, adjoint, composition, transform, canonical-map, hom, iterative and the normal form lemma (and, in Part 11c, in block-setting and the real/stability results)

NODE: bpN:p11:s-nf#data
KIND: definition
TITLE: Notation dictionary of Part 6 for the extended class
STATEMENT_SOURCE: blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:s-nf#data@L117-L117
PROOF_SOURCE: -
CONTRACT_ID: bpN:p11:s-nf#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: h holomorphic on V_R(I_c) (regarded as a function on D^e_{R,s} independent of (theta,x-tilde)); the data of bpN:p11:s-ext-class#data; p>1, q=p/(p-1)
SOURCE_QUANTIFIERS: R; K_a; alpha; L; Lambda; h; p
SOURCE_CONCLUSION: records the dictionary (D,r,K,alpha,L,Lambda,h)->({I_c},R,K_a,alpha,L,Lambda,h) of Part 6, K_a the analytic cut-off, q=p/(p-1), abar=2 pi alpha, kappa=2 pi K_a s; omega=d_I h
CONSTANT_SCOPE: p>1 arbitrary here; Part 11 uses p=9/8, q=9
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p6:setting, bpN:p6#data, bpN:p4:domains, bpN:p11:s-ext-class#data, bpN:p11:ext-class
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p6:setting | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:s-nf#data@L117-L117 | the Part 6 setting (D,r,K,alpha,L,Lambda,h) and omega=d_I h that is being translated
EDGE: bpN:p6#data | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:s-nf#data@L117-L117 | q=p/(p-1), abar=2 pi alpha, kappa=2 pi K_a s
EDGE: bpN:p4:domains | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:s-nf#data@L117-L117 | V_R(I_c) is V_R applied to the base set {I_c}
EDGE: bpN:p11:s-ext-class#data | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:s-nf#data@L117-L117 | I_c, R=r_B-scaled radii, the extended variables
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11b-partial-nf.tex#bpN:p11:s-nf#data@L117-L117 | D^e_{R,s}, on which h is regarded as a function
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11ab
REVIEWER: sol-review-N-f
LEAN_STATUS: PROVED
LEAN_REF: ExtNFHyp, liftFast (KAM/Nekhoroshev/Partial/Setting.lean)
LEAN_NOTE: audit N11-A-audit-1 PASS WITH NOTES
NOTE: section-data node for coverage item p11b:prose-L104-L104; consumed by hom, iterative and nf

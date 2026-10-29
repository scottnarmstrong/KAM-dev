NODE: bpP:p7:e-ift
KIND: external
TITLE: Real-analytic inverse function theorem
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:e-ift@L37-L38
PROOF_SOURCE: -
CONTRACT_ID: bpP:p7:e-ift
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: real-analytic maps between open sets of R^N
SOURCE_QUANTIFIERS: none (library fact)
SOURCE_CONCLUSION: real-analytic inverse function theorem: a real-analytic map with invertible differential at z0 is a real-analytic diffeomorphism from a neighbourhood of z0 onto an open set; an implicit equation Phi(F,x)=0 with d_F Phi!=0 has a locally unique real-analytic solution F(x); a bijective real-analytic map between open sets with everywhere invertible differential is a real-analytic diffeomorphism
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7
REVIEWER: sol-review-P-i
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: kept as external: adds analytic regularity and the implicit-equation and global-bijection forms to bpP:p1:ext-ift (C^1 inverse function theorem), so it is not an alias; related node bpP:p1:ext-ift

NODE: bpP:p7:e-dense
KIND: external
TITLE: bpP:p7:e-dense
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:e-dense@L42-L42
PROOF_SOURCE: -
CONTRACT_ID: bpP:p7:e-dense
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: f,g continuous on an open set U subset R^N; f=g on a dense subset of U
SOURCE_QUANTIFIERS: none (library fact)
SOURCE_CONCLUSION: f=g on all of U
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7
REVIEWER: sol-review-P-i
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p7:e-comp
KIND: external
TITLE: bpP:p7:e-comp
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:e-comp@L44-L44
PROOF_SOURCE: -
CONTRACT_ID: bpP:p7:e-comp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K subset V subset R^N, K compact, V open (K may be empty, V may be R^N)
SOURCE_QUANTIFIERS: K, V; then delta
SOURCE_CONCLUSION: there is delta>0 such that every point within max-norm distance <delta of some point of K lies in V
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7
REVIEWER: sol-review-P-i
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p7:kepler-data
KIND: definition
TITLE: Kepler data
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:kepler-data@L49-L58
PROOF_SOURCE: -
CONTRACT_ID: bpP:p7:kepler-data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: conv#data: m>0, kappa>0; (q,p) in R^2xR^2 with q!=0
SOURCE_QUANTIFIERS: m, kappa; then (q,p)
SOURCE_CONCLUSION: defines E_{m,kappa}(q,p)=l(p)^2/(2m)-kappa m/l(q), C=cr(q,p), a=-kappa m/(2E), Lambda=m sqrt(kappa a) (E<0); the prograde bound region K_{m,kappa}={q!=0,E<0,C>0} (open); on it e=sqrt(1-C^2/Lambda^2); D^m={(ell,g,Lambda,C): Lambda>C>0}; Q_{m,kappa}=S_{m,kappa} o Q^I(ell,g,Lambda/m,C/m) with S_{m,kappa}(Q,P)=(Q/kappa, m kappa P)
CONSTANT_SCOPE: none (m, kappa are data of the part)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p7:conv#data, I:bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p7:conv#data | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:kepler-data@L49-L49 | m, kappa, l, cr
EDGE: I:bpI:p7:orbit-maps | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:kepler-data@L54-L54 | Q^I in the definition of Q_{m,kappa}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7
REVIEWER: sol-review-P-i
LEAN_STATUS: PROVED
LEAN_REF: delaunayMK (KAM/Kepler/Mass.lean); scaleMK, energyMK, axisMK, actionMK, regionMK, isOpen_regionMK (KAM/Kepler/Energy.lean)
LEAN_NOTE: audit KEP-10 PASS WITH NOTES (delaunayMK) + KEP-1 PASS (addendum) (Energy definitions)
NOTE: the \frozen tag (keplerEnergy, keplerAxis, keplerAction, planeCross) records a statement about the Lean definitions, proved in bpP:p7:d25(d); the definition itself depends on none of them. The reference to bpP:p7:range (0<C<=Lambda, so that e is defined) is not an edge: range is a result about this definition

NODE: bpP:p7:range
KIND: lemma
TITLE: Range of the elements
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:range@L60-L62
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:range@L63-L67
CONTRACT_ID: bpP:p7:range
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (q,p) in K_{m,kappa}
SOURCE_QUANTIFIERS: m, kappa; (q,p) in K_{m,kappa}
SOURCE_CONCLUSION: 0<C<=Lambda, with equality iff the orbit is circular (l(q) constant); equivalently Gamma:=Lambda-C in [0,Lambda)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p7:rg-scale, stepP:p7:rg-lagrange, bpP:p7:kepler-data, bpP:p7:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p7:rg-scale | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:range@L64-L64 | proof step Scaling to strength one
EDGE: stepP:p7:rg-lagrange | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:range@L65-L65 | proof step Lagrange identity
EDGE: bpP:p7:kepler-data | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:range@L61-L61 | K, C, Lambda
EDGE: bpP:p7:conv#data | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:range@L61-L61 | m, kappa
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7
REVIEWER: sol-review-P-i
LEAN_STATUS: PROVED
LEAN_REF: cross_le_action, cross_eq_action_iff (KAM/Kepler/Mass.lean)
LEAN_NOTE: audit KEP-10 PASS WITH NOTES; equality case stated pointwise (q.p=0 and |q|=a), design D11
NOTE: -

NODE: stepP:p7:rg-scale
KIND: step
TITLE: Scaling to strength one
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:rg-scale@L64-L64
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:rg-scale@L64-L64
CONTRACT_ID: stepP:p7:rg-scale
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (Q,P)=S_{m,kappa}^{-1}(q,p)=(kappa q,p/(m kappa))
SOURCE_QUANTIFIERS: (q,p) in K_{m,kappa}
SOURCE_CONCLUSION: E_1(Q,P)=E_{m,kappa}(q,p)/(m kappa^2), cr(Q,P)=C/m, L:=Lambda/m=sqrt(-1/(2E_1(Q,P)))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:scaling, bpP:p7:kepler-data, bpP:p7:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:scaling | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:rg-scale@L64-L64 | dictionary E_kappa o S_kappa=kappa^2 E_1 and E_{m,kappa}=m E_kappa(q,p/m)
EDGE: bpP:p7:kepler-data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:rg-scale@L64-L64 | E_{m,kappa}, S_{m,kappa}, Lambda
EDGE: bpP:p7:conv#data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:rg-scale@L64-L64 | uses the positive mass/strength, physical-length or rotation conventions of the package
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7+sol-review-P-i
REVIEWER: sol-delta-P-i
LEAN_STATUS: PROVED
LEAN_REF: rg_scale (KAM/Kepler/ScalingNodes.lean)
LEAN_NOTE: audit GAP-P7 round 2 PASS WITH NOTES
NOTE: -

NODE: stepP:p7:rg-lagrange
KIND: step
TITLE: Lagrange identity
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:rg-lagrange@L65-L66
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:rg-lagrange@L65-L66
CONTRACT_ID: stepP:p7:rg-lagrange
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed data and source premises of bpP:p7:range; (q,p) in K_{m,kappa}; Q,P,L are scaled variables. Earlier proof facts and cited results are supplied through DEPS, not extra hypotheses.
SOURCE_QUANTIFIERS: (q,p) in K_{m,kappa}
SOURCE_CONCLUSION: cr(Q,P)^2<=L^2 with equality iff Q.P=0 and l(Q)=L^2, hence C<=Lambda with equality iff circular
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p7:rg-scale, bpP:p7:conv#data, bpP:p7:kepler-data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p7:rg-scale | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:rg-lagrange@L65-L65 | 1/2 l(P)^2=E_1+1/r and L=sqrt(-1/(2E_1))
EDGE: bpP:p7:conv#data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:rg-lagrange@L65-L65 | cr and l
EDGE: bpP:p7:kepler-data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:rg-lagrange@L66-L66 | C, Lambda and the region K_{m,kappa} of the conclusion use the Kepler data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7+sol-delta-P-i
REVIEWER: sol-delta-P-q
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: route substitution (D27, ruling OVERNIGHT 01:20): the Lean proof of the PROVED parent range avoids this step
NOTE: -

NODE: bpP:p7:kepler
KIND: proposition
TITLE: Planar Kepler problem, mass $m$, strength $\kappa$
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:kepler@L69-L81
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:kepler@L82-L90
CONTRACT_ID: bpP:p7:kepler
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: conv#data; D^m and Q_{m,kappa} as in Definition bpP:p7:kepler-data; (c) Lambda>0, 0<C<=Lambda, g in R, with Q extended to C=Lambda by the same formulas
SOURCE_QUANTIFIERS: m, kappa; (a),(b),(d) on D^m; (c) Lambda,C,g
SOURCE_CONCLUSION: (a) Q_{m,kappa} is real analytic, 2pi-periodic in ell and g, induces a real-analytic diffeomorphism (R/2piZ)^2 x {Lambda>C>0} -> K*_{m,kappa}={C<Lambda}, and Q^*(sum dp^dq)=dLambda^dell+dC^dg; (b) q=a((cos u-e)e_g+sqrt(1-e^2) sin u J_0e_g), l(q)=a(1-e cos u), cr=C, E=-kappa^2m^3/(2Lambda^2), a=Lambda^2/(m^2 kappa), e=sqrt(1-C^2/Lambda^2), u=u_R(ell,e); (c) mean values over ell: 1/a, m^2 kappa/a, a(1+e^2/2); (d) E o Q=h_m(Lambda)=-kappa^2m^3/(2Lambda^2), h_m'=kappa^2m^3/Lambda^3=sqrt(kappa)a^{-3/2}, Hamilton equations ell'=h_m', g'=Lambda'=C'=0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p7:ke-chart, stepP:p7:ke-form, stepP:p7:ke-b, stepP:p7:ke-c, stepP:p7:ke-d, bpP:p7:kepler-data, I:bpI:p7:kepler-eq, bpI:p7:circular, I:bpI:p7:orbit-maps, bpP:p7:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p7:ke-chart | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:kepler@L85-L85 | proof step (a) Chart
EDGE: stepP:p7:ke-form | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:kepler@L86-L86 | proof step (a) The form
EDGE: stepP:p7:ke-b | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:kepler@L87-L87 | proof step (b)
EDGE: stepP:p7:ke-c | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:kepler@L88-L88 | proof step (c)
EDGE: stepP:p7:ke-d | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:kepler@L89-L89 | proof step (d)
EDGE: bpP:p7:kepler-data | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:kepler@L70-L70 | D^m, Q_{m,kappa}, K, elements
EDGE: I:bpI:p7:kepler-eq | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:kepler@L74-L74 | u=u_R(ell,e) of Kepler equation
EDGE: bpI:p7:circular | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:kepler@L76-L76 | extension to the circular case C=Lambda
EDGE: I:bpI:p7:orbit-maps | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:kepler@L83-L83 | (L,G) in C_0 of the Delaunay orbit map
EDGE: bpP:p7:conv#data | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:kepler@L70-L70 | m, kappa
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7
REVIEWER: sol-review-P-i
LEAN_STATUS: PROVED
LEAN_REF: delaunayMK_symplectic, analyticOnNhd_delaunayMK, delaunayMK_periodic, delaunayMK_eq_iff, delaunayMK_localDiffeo, delaunayMK_image, delaunayMK_identities, delaunayMK_position, hasDerivAt_keplerEnergy_action, delaunayMK_means (KAM/Kepler/Mass.lean)
LEAN_NOTE: audit KEP-10 PASS WITH NOTES; (a)-(d); quotient diffeomorphism as exact image + injectivity mod 2piZ + analytic local inverses (design D3/B6)
NOTE: -

NODE: stepP:p7:ke-chart
KIND: step
TITLE: (a) Chart
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ke-chart@L85-L85
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ke-chart@L85-L85
CONTRACT_ID: stepP:p7:ke-chart
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed data and source premises of bpP:p7:kepler. Earlier proof facts and cited results are supplied through DEPS, not extra hypotheses.
SOURCE_QUANTIFIERS: fixed positive m,kappa; the entire chart on D^m, modulo 2pi in ell and g
SOURCE_CONCLUSION: Q_{m,kappa} is a real-analytic diffeomorphism of (R/2piZ)^2 x {Lambda>C>0} onto K*_{m,kappa}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p7:rg-scale, I:bpI:p7:chart, I:bpI:p7:elements, bpP:p7:kepler-data, bpP:p7:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p7:rg-scale | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ke-chart@L85-L85 | E_{m,kappa}=m kappa^2 E_1, cr(q,p)=m cr(Q,P), Lambda=m L
EDGE: I:bpI:p7:chart | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ke-chart@L85-L85 | Q^I induces a real-analytic diffeomorphism onto C
EDGE: I:bpI:p7:elements | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ke-chart@L85-L85 | the region C={E_1<0,cr>0,cr<L} and its elements
EDGE: bpP:p7:kepler-data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ke-chart@L85-L85 | K*_{m,kappa}, S_{m,kappa}, Q_{m,kappa}
EDGE: bpP:p7:conv#data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ke-chart@L85-L85 | uses the positive mass/strength, physical-length or rotation conventions of the package
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7+sol-review-P-i
REVIEWER: sol-delta-P-i
LEAN_STATUS: PROVED
LEAN_REF: delaunayMK_periodic, delaunayMK_eq_iff, delaunayMK_localDiffeo, delaunayMK_image, analyticOnNhd_delaunayMK (KAM/Kepler/Mass.lean)
LEAN_NOTE: audit KEP-10 PASS WITH NOTES; named kepler (a)
NOTE: -

NODE: stepP:p7:ke-form
KIND: step
TITLE: (a) The form
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ke-form@L86-L86
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ke-form@L86-L86
CONTRACT_ID: stepP:p7:ke-form
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed data and source premises of bpP:p7:kepler. Earlier proof facts and cited results are supplied through DEPS, not extra hypotheses.
SOURCE_QUANTIFIERS: (ell,g,Lambda,C) in D^m
SOURCE_CONCLUSION: Q_{m,kappa}^*(sum dp^dq)=dLambda^dell+dC^dg
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: I:bpI:p7:symplectic, bpP:p7:kepler-data, bpP:p7:conv#data, I:bpI:p7:x-forms
ROUTES: -
ROUTE_FOR: -
EDGE: I:bpI:p7:symplectic | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ke-form@L86-L86 | (Q^I)^*(sum dq^dp)=dell^dL+dg^dG
EDGE: bpP:p7:kepler-data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ke-form@L86-L86 | S_{m,kappa}
EDGE: bpP:p7:conv#data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ke-form@L86-L86 | uses the positive mass/strength, physical-length or rotation conventions of the package
EDGE: I:bpI:p7:x-forms | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ke-form@L86-L86 | pull-back, composition and exterior-form calculus used in this calculation
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7+sol-review-P-i
REVIEWER: sol-delta-P-i
LEAN_STATUS: PROVED
LEAN_REF: delaunayMK_symplectic (KAM/Kepler/Mass.lean)
LEAN_NOTE: audit KEP-10 PASS WITH NOTES; named kepler (a) form
NOTE: -

NODE: stepP:p7:ke-b
KIND: step
TITLE: (b)
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ke-b@L87-L87
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ke-b@L87-L87
CONTRACT_ID: stepP:p7:ke-b
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (Q,P)=Q^I(ell,g,L,G), (q,p)=S_{m,kappa}(Q,P), L=Lambda/m, G=C/m
SOURCE_QUANTIFIERS: (ell,g,Lambda,C) in D^m
SOURCE_CONCLUSION: l(q)=a(1-e cos u), q=a((cos u-e)e_g+sqrt(1-e^2) sin u J_0 e_g), cr=C, E=-kappa^2m^3/(2Lambda^2), a=Lambda^2/(m^2 kappa) agrees with Definition kepler-data
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: I:bpI:p7:orbit-identities, I:bpI:p7:orbit-maps, stepP:p7:rg-scale, bpP:p7:kepler-data, bpP:p7:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: I:bpI:p7:orbit-identities | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ke-b@L87-L87 | l(Q)=L^2(1-e cos u), E_1=-1/(2L^2), cr(Q,P)=G
EDGE: I:bpI:p7:orbit-maps | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ke-b@L87-L87 | Q=R(g)(X,Y)
EDGE: stepP:p7:rg-scale | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ke-b@L87-L87 | E_{m,kappa}=m kappa^2 E_1, scaling
EDGE: bpP:p7:kepler-data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ke-b@L87-L87 | a, E, S_{m,kappa}
EDGE: bpP:p7:conv#data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ke-b@L87-L87 | uses the positive mass/strength, physical-length or rotation conventions of the package
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7+sol-review-P-i
REVIEWER: sol-delta-P-i
LEAN_STATUS: PROVED
LEAN_REF: delaunayMK_identities, delaunayMK_position (KAM/Kepler/Mass.lean)
LEAN_NOTE: audit KEP-10 PASS WITH NOTES; named kepler (b)
NOTE: -

NODE: stepP:p7:ke-c
KIND: step
TITLE: (c)
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ke-c@L88-L88
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ke-c@L88-L88
CONTRACT_ID: stepP:p7:ke-c
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed data and source premises of bpP:p7:kepler; clause (c): Lambda>0, 0<C<=Lambda, g in R. Earlier proof facts and cited results are supplied through DEPS, not extra hypotheses.
SOURCE_QUANTIFIERS: Lambda>0, 0<C<=Lambda, g
SOURCE_CONCLUSION: mean values 1/a, m^2 kappa/a, a(1+e^2/2) of 1/l(q), l(p)^2, l(q)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:means, bpI:p7:circular, stepP:p7:ke-b, bpP:p7:conv#data, bpP:p7:kepler-data
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:means | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ke-c@L88-L88 | mean values for strength one
EDGE: bpI:p7:circular | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ke-c@L88-L88 | circular case C=Lambda
EDGE: stepP:p7:ke-b | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ke-c@L88-L88 | a=L^2/kappa and the scaling of step (b)
EDGE: bpP:p7:conv#data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ke-c@L88-L88 | uses the positive mass/strength, physical-length or rotation conventions of the package
EDGE: bpP:p7:kepler-data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ke-c@L88-L88 | the scaled elements a and Lambda and their mass/strength dictionary
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7+sol-delta-P-i
REVIEWER: sol-delta-P-q
LEAN_STATUS: PROVED
LEAN_REF: delaunayMK_means (KAM/Kepler/Mass.lean)
LEAN_NOTE: audit KEP-10 PASS WITH NOTES; named kepler (c)
NOTE: -

NODE: stepP:p7:ke-d
KIND: step
TITLE: (d)
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ke-d@L89-L89
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ke-d@L89-L89
CONTRACT_ID: stepP:p7:ke-d
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed data and source premises of bpP:p7:kepler. Earlier proof facts and cited results are supplied through DEPS, not extra hypotheses.
SOURCE_QUANTIFIERS: (ell,g,Lambda,C) in D^m
SOURCE_CONCLUSION: E o Q=h_m(Lambda); h_m'=kappa^2m^3/Lambda^3=sqrt(kappa)a^{-3/2}; Hamilton equations of h_m in (ell,g;Lambda,C) are ell'=h_m', g'=Lambda'=C'=0 and transport to the Kepler flow
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p7:ke-b, stepP:p7:ke-form, bpP:p0:hamsymp#hamiltonianVectorField, bpP:p1:chart-field, bpP:p7:conv#data, bpP:p7:kepler-data, stepP:p7:ke-chart
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p7:ke-b | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ke-d@L89-L89 | value of E o Q
EDGE: stepP:p7:ke-form | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ke-d@L89-L89 | symplectic with factor one in (ell,g;Lambda,C)
EDGE: bpP:p0:hamsymp#hamiltonianVectorField | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ke-d@L89-L89 | Hamilton equations X_H=(d_pH,-d_qH)
EDGE: bpP:p1:chart-field | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ke-d@L89-L89 | transport of the equations by the chart
EDGE: bpP:p7:conv#data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ke-d@L89-L89 | uses the positive mass/strength, physical-length or rotation conventions of the package
EDGE: bpP:p7:kepler-data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ke-d@L89-L89 | Q_{m,kappa}, its domain D^m and E_{m,kappa}
EDGE: stepP:p7:ke-chart | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ke-d@L89-L89 | analytic regularity of Q_{m,kappa} from clause (a), needed with ke-form to apply chart-field
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7+sol-delta-P-i
REVIEWER: sol-delta-P-q
LEAN_STATUS: PROVED
LEAN_REF: delaunayMK_identities, hasDerivAt_keplerEnergy_action (KAM/Kepler/Mass.lean)
LEAN_NOTE: audit KEP-10 PASS WITH NOTES; named kepler (d)
NOTE: -

NODE: bpP:p7:regular-kepler
KIND: proposition
TITLE: Regular Kepler equation
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:regular-kepler@L99-L108
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:regular-kepler@L109-L115
CONTRACT_ID: bpP:p7:regular-kepler
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: v in R^2, F in R; Phi(F,v)=F-v_0 sin F+v_1 cos F; J(F,v)=d_F Phi=1-v.(cos F,sin F); (b) N_0={(lambda,v) in CxC^2: ¦Im lambda¦<1/4, ¦v_0¦+¦v_1¦<1/4}, S={F in C: ¦Im F¦<=1}
SOURCE_QUANTIFIERS: (a) all real v with l(v)<1 and real lambda; (b) all complex (lambda,v) in N_0; (c) all real lambda,g and e in (0,1), v=e e_g
SOURCE_CONCLUSION: (a) for l(v)<1: J>=1-l(v)>0, F -> Phi(F,v) a real-analytic increasing bijection of R with Phi(F+2pi)=Phi+2pi; unique real F(lambda,v) with Phi=lambda, real analytic, F(lambda+2pi,v)=F+2pi, F(lambda,0)=lambda, d_lambda F=1/J, d_{v_0}F=sin F/J, d_{v_1}F=-cos F/J; (b) unique holomorphic F:N_0->S with Phi(F(lambda,v),v)=lambda, ¦J¦>=1-(1/4)cosh(1)>3/5, same formulas, F real at real points and equal to (a); (c) for v=e e_g, e in (0,1): F(lambda,v)=g+u_R(lambda-g,e)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p7:rk-mono, stepP:p7:rk-an, stepP:p7:rk-contr, stepP:p7:rk-hol, stepP:p7:rk-rel, I:bpI:p7:kepler-eq, bpP:p7:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p7:rk-mono | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:regular-kepler@L110-L110 | proof step (a) Monotonicity
EDGE: stepP:p7:rk-an | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:regular-kepler@L111-L111 | proof step (a) Analyticity
EDGE: stepP:p7:rk-contr | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:regular-kepler@L112-L112 | proof step (b) Contraction
EDGE: stepP:p7:rk-hol | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:regular-kepler@L113-L113 | proof step (b) Holomorphy
EDGE: stepP:p7:rk-rel | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:regular-kepler@L114-L114 | proof step (c) Relation
EDGE: I:bpI:p7:kepler-eq | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:regular-kepler@L105-L105 | u_R of Kepler equation in (c)
EDGE: bpP:p7:conv#data | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:regular-kepler@L100-L100 | uses the physical length or rotation notation fixed by this package
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7+sol-review-P-i
REVIEWER: sol-delta-P-i
LEAN_STATUS: PROVED
LEAN_REF: keplerPhi_shift, keplerPhi_zero, keplerJac_ge, keplerJac_pos, keplerPhi_strictMono, keplerPhi_bijective, keplerPhi_keplerLong, keplerLong_unique, keplerLong_shift, keplerLong_zero_vec, analyticOnNhd_keplerLong, hasDerivAt_keplerLong_lambda, fderiv_keplerLong_vec, keplerLong_eq_add_eccAnom (KAM/Kepler/Equation.lean); regularKepler_complex, keplerLongC_ofReal, keplerLongC_shift, regularKepler_jac_bound, fderiv_keplerLongC_vec (KAM/Kepler/KeplerTube.lean)
LEAN_NOTE: audit KEP-2 PASS (a),(c) + KEP-4 PASS WITH NOTES (b)
NOTE: -

NODE: stepP:p7:rk-mono
KIND: step
TITLE: (a) Monotonicity
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:rk-mono@L110-L110
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:rk-mono@L110-L110
CONTRACT_ID: stepP:p7:rk-mono
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed data and source premises of bpP:p7:regular-kepler; real v with l(v)<1. Earlier proof facts and cited results are supplied through DEPS, not extra hypotheses.
SOURCE_QUANTIFIERS: v with l(v)<1; F in R
SOURCE_CONCLUSION: J>=1-l(v)>0; Phi(.,v) strictly increasing bijection of R; Phi(F+2pi,v)=Phi+2pi; Phi(F,0)=F
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p7:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p7:conv#data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:rk-mono@L110-L110 | uses the positive mass/strength, physical-length or rotation conventions of the package
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7+sol-review-P-i
REVIEWER: sol-delta-P-i
LEAN_STATUS: PROVED
LEAN_REF: keplerJac_ge, keplerJac_pos, keplerPhi_strictMono, keplerPhi_bijective, keplerPhi_shift (KAM/Kepler/Equation.lean)
LEAN_NOTE: audit KEP-2 PASS; named regular-kepler (a)
NOTE: -

NODE: stepP:p7:rk-an
KIND: step
TITLE: (a) Analyticity
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:rk-an@L111-L111
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:rk-an@L111-L111
CONTRACT_ID: stepP:p7:rk-an
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed data and source premises of bpP:p7:regular-kepler; real (lambda,v) with l(v)<1. Earlier proof facts and cited results are supplied through DEPS, not extra hypotheses.
SOURCE_QUANTIFIERS: (lambda_0,v_0) with l(v_0)<1
SOURCE_CONCLUSION: F is real analytic; J d_lambda F=1, J d_{v_0}F=sin F, J d_{v_1}F=-cos F
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p7:e-ift, stepP:p7:rk-mono, bpP:p7:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p7:e-ift | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:rk-an@L111-L111 | real-analytic implicit function theorem
EDGE: stepP:p7:rk-mono | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:rk-an@L111-L111 | J>0 and uniqueness of the global solution
EDGE: bpP:p7:conv#data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:rk-an@L111-L111 | uses the positive mass/strength, physical-length or rotation conventions of the package
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7+sol-review-P-i
REVIEWER: sol-delta-P-i
LEAN_STATUS: PROVED
LEAN_REF: analyticOnNhd_keplerLong, hasDerivAt_keplerLong_lambda, fderiv_keplerLong_vec, keplerLong_shift, keplerLong_zero_vec (KAM/Kepler/Equation.lean)
LEAN_NOTE: audit KEP-2 PASS; named regular-kepler (a)
NOTE: -

NODE: stepP:p7:rk-contr
KIND: step
TITLE: (b) Contraction
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:rk-contr@L112-L112
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:rk-contr@L112-L112
CONTRACT_ID: stepP:p7:rk-contr
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: beta_{lambda,v}(F)=lambda+v_0 sin F-v_1 cos F; F in S; (lambda,v) in N_0
SOURCE_QUANTIFIERS: (lambda,v) in N_0
SOURCE_CONCLUSION: beta maps S into S and is a 0.39-contraction of the closed convex set S; unique fixed point F(lambda,v) in S
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p1:ext-banach, K:bp:p1:ext-mvt, I:stepI:p7:ke-trig
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p1:ext-banach | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:rk-contr@L112-L112 | Banach fixed point theorem
EDGE: K:bp:p1:ext-mvt | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:rk-contr@L112-L112 | mean value inequality on the convex set S
EDGE: I:stepI:p7:ke-trig | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:rk-contr@L112-L112 | ¦sin F¦,¦cos F¦<=cosh Im F
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7
REVIEWER: sol-review-P-i
LEAN_STATUS: PROVED
LEAN_REF: existsUnique_keplerOp (KAM/Kepler/EquationComplex.lean); Tube.keplerData_regular (KAM/Kepler/KeplerTube.lean)
LEAN_NOTE: audit KEP-3/KEP-4 PASS WITH NOTES; named P rk-contr
NOTE: -

NODE: stepP:p7:rk-hol
KIND: step
TITLE: (b) Holomorphy, real points
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:rk-hol@L113-L113
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:rk-hol@L113-L113
CONTRACT_ID: stepP:p7:rk-hol
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed data and source premises of bpP:p7:regular-kepler; complex (lambda,v) in N_0. Earlier proof facts and cited results are supplied through DEPS, not extra hypotheses.
SOURCE_QUANTIFIERS: (lambda,v) in N_0
SOURCE_CONCLUSION: F is holomorphic on N_0; real at real points and equal to the real solution; ¦J¦>3/5; derivative formulas hold
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p7:rk-contr, K:bp:p1:ext-banach, I:bpI:p7:x-hol, I:bpI:p7:x-weier, stepP:p7:rk-mono, stepP:p7:rk-an
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p7:rk-contr | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:rk-hol@L113-L113 | contraction and fixed point
EDGE: K:bp:p1:ext-banach | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:rk-hol@L113-L113 | uniform geometric convergence of the Banach iteration
EDGE: I:bpI:p7:x-hol | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:rk-hol@L113-L113 | holomorphic calculus
EDGE: I:bpI:p7:x-weier | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:rk-hol@L113-L113 | locally uniform limit of holomorphic functions is holomorphic
EDGE: stepP:p7:rk-mono | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:rk-hol@L113-L113 | uniqueness of the real solution of (a)
EDGE: stepP:p7:rk-an | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:rk-hol@L113-L113 | same implicit differentiation as in (a)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7+sol-review-P-i
REVIEWER: sol-delta-P-i
LEAN_STATUS: PROVED
LEAN_REF: keplerSol_analyticOnNhd (KAM/Kepler/EquationComplex.lean); regularKepler_complex, keplerLongC_ofReal, regularKepler_jac_bound, fderiv_keplerLongC_vec (KAM/Kepler/KeplerTube.lean)
LEAN_NOTE: audit KEP-3/KEP-4 PASS WITH NOTES; named P rk-hol
NOTE: -

NODE: stepP:p7:rk-rel
KIND: step
TITLE: (c) Relation
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:rk-rel@L114-L114
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:rk-rel@L114-L114
CONTRACT_ID: stepP:p7:rk-rel
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: v=e e_g, e in (0,1); F'=g+u_R(lambda-g,e)
SOURCE_QUANTIFIERS: lambda, e, g
SOURCE_CONCLUSION: F(lambda,v)=g+u_R(lambda-g,e)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: I:bpI:p7:kepler-eq, stepP:p7:rk-mono, bpP:p7:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: I:bpI:p7:kepler-eq | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:rk-rel@L114-L114 | u_R solves u-e sin u=ell
EDGE: stepP:p7:rk-mono | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:rk-rel@L114-L114 | uniqueness of the solution in (a)
EDGE: bpP:p7:conv#data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:rk-rel@L114-L114 | uses the positive mass/strength, physical-length or rotation conventions of the package
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7+sol-review-P-i
REVIEWER: sol-delta-P-i
LEAN_STATUS: PROVED
LEAN_REF: keplerLong_eq_add_eccAnom (KAM/Kepler/Equation.lean)
LEAN_NOTE: audit KEP-2 PASS; named regular-kepler (c)
NOTE: -

NODE: bpP:p7:poincare-def
KIND: definition
TITLE: Poincar\'e chart of one planet
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:poincare-def@L119-L129
PROOF_SOURCE: -
CONTRACT_ID: bpP:p7:poincare-def
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m>0, kappa>0
SOURCE_QUANTIFIERS: m, kappa; then (lambda,xi,Lambda,eta) in the domain O
SOURCE_CONCLUSION: defines O={(lambda,xi,Lambda,eta) in R^4: Lambda>0, Gamma<Lambda} with Gamma=(xi^2+eta^2)/2 and on O: k=1-Gamma/Lambda in (0,1], v=sqrt((1-Gamma/(2Lambda))/Lambda)(xi,eta), a=Lambda^2/(m^2 kappa), F=F(lambda,v), c=(cos F,sin F), J=1-v.c, q=a(k c-v+(v.c)/(1+k) v), p=(m^2 kappa/(Lambda J))(J_0 c-(v.c)/(1+k) J_0 v), Psi_{m,kappa}=(q,p)
CONSTANT_SCOPE: none (m, kappa are fixed data)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p7:regular-kepler, bpP:p7:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p7:regular-kepler | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:poincare-def@L122-L122 | F=F(lambda,v) of Prop regular-kepler(a)
EDGE: bpP:p7:conv#data | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:poincare-def@L120-L120 | m, kappa, Gamma, J_0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7
REVIEWER: sol-review-P-i
LEAN_STATUS: PROVED
LEAN_REF: poincareGamma, poincareK, poincareV, poincareF, poincare, poincareDom, isOpen_poincareDom (KAM/Planetary/Poincare/Chart.lean)
LEAN_NOTE: audit P7-1 PASS WITH NOTES
NOTE: the \frozen tag (secularEccVector, secularRoot, secularGamma, secularAxis, ellipsePosition, ellipseMomentum, keplerMeanLongitude, longitudeJacobian) records that these Lean definitions are this chart for kappa=1: a statement about them, proved in bpP:p7:d25, so no edge here; the reference to bpP:p7:d25 is a forward pointer (cycle d25 <-> poincare-def avoided)

NODE: bpP:p7:o-facts
KIND: lemma
TITLE: Elementary facts on $\mathcal O$
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:o-facts@L131-L133
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:o-facts@L134-L136
CONTRACT_ID: bpP:p7:o-facts
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (lambda,xi,Lambda,eta) in O; (xi,eta)=rho e_g with rho=sqrt(2Gamma) for (xi,eta)!=0
SOURCE_QUANTIFIERS: points of O
SOURCE_CONCLUSION: Gamma>=0, 0<k<=1, l(v)^2=1-k^2 (so l(v)<1 and F defined, real analytic); J>=1-l(v)>0; radicand of v positive; v.c=e cos(F-g), l(v)=e with e=sqrt(1-k^2); for (xi,eta)!=0: v=e e_g and Gamma=Lambda-C with C=Lambda k
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p7:poincare-def, bpP:p7:regular-kepler, bpP:p7:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p7:poincare-def | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:o-facts@L131-L131 | O, k, v, F, J
EDGE: bpP:p7:regular-kepler | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:o-facts@L132-L132 | F defined and real analytic; J>=1-l(v); v.c
EDGE: bpP:p7:conv#data | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:o-facts@L132-L132 | uses the physical length or rotation notation fixed by this package
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7+sol-review-P-i
REVIEWER: sol-delta-P-i
LEAN_STATUS: PROVED
LEAN_REF: poincare_facts, poincare_facts_polar (KAM/Planetary/Poincare/Chart.lean); keplerJac_ge (KAM/Kepler/Equation.lean)
LEAN_NOTE: audit P7-1 PASS WITH NOTES; J lower bound via imported keplerJac_ge (packaging note)
NOTE: -

NODE: bpP:p7:poincare
KIND: theorem
TITLE: Poincar\'e chart, analytic through $e=0$
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:poincare@L138-L148
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:poincare@L149-L164
CONTRACT_ID: bpP:p7:poincare
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Psi=Psi_{m,kappa}:O->R^2xR^2 as in Definition poincare-def
SOURCE_QUANTIFIERS: m, kappa; then points of O
SOURCE_CONCLUSION: (a) Psi real analytic on O including xi=eta=0, 2pi-periodic in lambda; (b) for (xi,eta)=rho e_g, rho>0: Psi=Q_{m,kappa}(lambda-g,g,Lambda,Lambda-Gamma), F=g+u; (c) Omega(D Psi u,D Psi w)=Omega(u,w) on all of O, Psi^*Omega_cart=dLambda^dlambda+deta^dxi, Psi a 1-chart on O, D Psi invertible; (d) Psi(O) subset K_{m,kappa}; E=-kappa^2m^3/(2Lambda^2), a=Lambda^2/(m^2 kappa), action Lambda, cr=Lambda-Gamma=Lambda k, kappa^{-1}[(l(p)^2/m^2-kappa/l(q))q-(q.p/m^2)p] = v; (e) Psi:O->K_{m,kappa} onto, Psi(w')=Psi(w) iff (xi,Lambda,eta) equal and lambda'-lambda in 2piZ; induced map O/(2piZ x {0})->K_{m,kappa} a real-analytic diffeomorphism with inverse Lambda=m sqrt(kappa a), Gamma=Lambda-cr(q,p), v the rescaled LRL expression, (xi,eta)=v/s with s=sqrt((1-Gamma/(2Lambda))/Lambda), c=(k Id+vv^T/(1+k))^{-1}(q/a+v), F=arg c and lambda=Phi(F,v) modulo 2pi; (f) at xi=eta=0: v=0, k=1, F=lambda, q=a(cos lambda,sin lambda), p=m sqrt(kappa/a)(-sin lambda,cos lambda), the circular point for Lambda=m sqrt(kappa a)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p7:po-an, stepP:p7:po-del, stepP:p7:po-symp, stepP:p7:po-dense, stepP:p7:po-el, stepP:p7:po-bij, stepP:p7:po-circ, bpP:p7:poincare-def, bpP:p1:chart, bpP:p7:kepler-data, bpP:p0:circular#circularPoint, bpP:p7:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p7:po-an | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:poincare@L150-L150 | proof step (a)
EDGE: stepP:p7:po-del | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:poincare@L151-L151 | proof step (b) Delaunay
EDGE: stepP:p7:po-symp | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:poincare@L156-L156 | proof step (c) on Gamma>0
EDGE: stepP:p7:po-dense | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:poincare@L157-L157 | proof step (c) all of O
EDGE: stepP:p7:po-el | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:poincare@L158-L158 | proof step (d)
EDGE: stepP:p7:po-bij | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:poincare@L160-L160 | proof step (e)
EDGE: stepP:p7:po-circ | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:poincare@L163-L163 | proof step (f)
EDGE: bpP:p7:poincare-def | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:poincare@L139-L139 | Psi
EDGE: bpP:p1:chart | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:poincare@L143-L143 | 1-chart in the sense of Definition chart
EDGE: bpP:p7:kepler-data | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:poincare@L144-L144 | K_{m,kappa}, E, a, action, Q_{m,kappa}
EDGE: bpP:p0:circular#circularPoint | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:poincare@L146-L146 | (f): the circular point
EDGE: bpP:p7:conv#data | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:poincare@L143-L143 | Omega_cart, Omega_chart
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7+sol-review-P-i
REVIEWER: sol-delta-P-i
LEAN_STATUS: PROVED
LEAN_REF: analyticOnNhd_poincare, poincare_periodic (KAM/Planetary/Poincare/Chart.lean); poincare_eq_delaunayMK, poincare_symplectic, poincare_elements, poincare_circular (KAM/Planetary/Poincare/Symplectic.lean); poincare_eq_iff, poincare_localDiffeo, poincare_image, poincareInv, poincareInv_poincare, poincare_poincareInv (KAM/Planetary/Poincare/Bijective.lean)
LEAN_NOTE: audit P7-1/P7-2/P7-3 PASS WITH NOTES; (e) quotient diffeomorphism as image + injectivity mod 2piZ + analytic local inverse + explicit inverse (design B6)
NOTE: -

NODE: stepP:p7:po-an
KIND: step
TITLE: (a)
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-an@L150-L150
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-an@L150-L150
CONTRACT_ID: stepP:p7:po-an
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed data and source premises of bpP:p7:poincare. Earlier proof facts and cited results are supplied through DEPS, not extra hypotheses.
SOURCE_QUANTIFIERS: points of O
SOURCE_CONCLUSION: Psi real analytic on O including xi=eta=0 and 2pi-periodic in lambda
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p7:o-facts, bpP:p7:regular-kepler, bpP:p7:poincare-def, bpP:p1:ext-comp
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p7:o-facts | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-an@L150-L150 | positive radicand, l(v)<1, Lambda J>0
EDGE: bpP:p7:regular-kepler | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-an@L150-L150 | F real analytic and F(lambda+2pi,v)=F+2pi
EDGE: bpP:p7:poincare-def | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-an@L150-L150 | q,p as rational expressions
EDGE: bpP:p1:ext-comp | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-an@L150-L150 | real-analytic composition F(lambda,v(xi,eta,Lambda)), and sums/products of analytic ingredients
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7+sol-delta-P-i
REVIEWER: sol-delta-P-q
LEAN_STATUS: PROVED
LEAN_REF: analyticOnNhd_poincare, poincare_periodic (KAM/Planetary/Poincare/Chart.lean)
LEAN_NOTE: audit P7-1 PASS WITH NOTES; named poincare (a)
NOTE: -

NODE: stepP:p7:po-del
KIND: step
TITLE: (b) Delaunay on $\Gamma>0$
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-del@L151-L155
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-del@L151-L155
CONTRACT_ID: stepP:p7:po-del
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed positive m,kappa and chart data of bpP:p7:poincare; w=(lambda,xi,Lambda,eta) in O with Gamma>0; (xi,eta)=rho e_g, rho>0; l=lambda-g, C=Lambda-Gamma=Lambda k, L=Lambda/m, G=C/m
SOURCE_QUANTIFIERS: lambda, g, Lambda, rho>0
SOURCE_CONCLUSION: Psi(lambda,xi,Lambda,eta)=Q_{m,kappa}(lambda-g,g,Lambda,Lambda-Gamma), with F=g+u, u=u_R(lambda-g,e)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p7:o-facts, bpP:p7:regular-kepler, bpP:p7:kepler, I:bpI:p7:orbit-maps, bpP:p7:poincare-def, bpP:p7:kepler-data, bpP:p7:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p7:o-facts | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-del@L151-L151 | v=e e_g, e=sqrt(1-k^2)
EDGE: bpP:p7:regular-kepler | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-del@L151-L151 | (c): F=g+u_R
EDGE: bpP:p7:kepler | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-del@L153-L153 | (b): position of the Kepler orbit
EDGE: I:bpI:p7:orbit-maps | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-del@L155-L155 | P=R(g)(-sin u,k cos u)/(L J)
EDGE: bpP:p7:poincare-def | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-del@L151-L151 | q, p formulas
EDGE: bpP:p7:kepler-data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-del@L155-L155 | S_{m,kappa}, Q_{m,kappa}
EDGE: bpP:p7:conv#data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-del@L151-L151 | uses the positive mass/strength, physical-length or rotation conventions of the package
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7+sol-delta-P-i
REVIEWER: sol-delta-P-q
LEAN_STATUS: PROVED
LEAN_REF: poincare_eq_delaunayMK (KAM/Planetary/Poincare/Symplectic.lean)
LEAN_NOTE: audit P7-2 PASS WITH NOTES; named poincare (b)
NOTE: -

NODE: stepP:p7:po-symp
KIND: step
TITLE: (c) Symplecticity on $\{\Gamma>0\}$
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-symp@L156-L156
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-symp@L156-L156
CONTRACT_ID: stepP:p7:po-symp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed data and source premises of bpP:p7:poincare; w in O with Gamma>0; a local argument branch is constructed. Earlier proof facts and cited results are supplied through DEPS, not extra hypotheses.
SOURCE_QUANTIFIERS: points of A
SOURCE_CONCLUSION: Psi^*Omega_cart=dLambda^dlambda+deta^dxi on A
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p7:po-del, bpP:p7:kepler, bpP:p7:conv#data, I:bpI:p7:x-forms, bpP:p7:poincare-def
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p7:po-del | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-symp@L156-L156 | Psi=Q_{m,kappa} o T on A
EDGE: bpP:p7:kepler | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-symp@L156-L156 | (a): Q^*(sum dp^dq)=dLambda^dell+dC^dg
EDGE: bpP:p7:conv#data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-symp@L156-L156 | Omega_cart, d eta^d xi
EDGE: I:bpI:p7:x-forms | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-symp@L156-L156 | pull-back, composition and exterior-form calculus used in this calculation
EDGE: bpP:p7:poincare-def | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-symp@L156-L156 | uses the domain O and Gamma=(xi^2+eta^2)/2
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7+sol-review-P-i
REVIEWER: sol-delta-P-i
LEAN_STATUS: PROVED
LEAN_REF: poincare_symplectic (KAM/Planetary/Poincare/Symplectic.lean)
LEAN_NOTE: audit P7-2 PASS WITH NOTES; named poincare (c); holds on all of poincareDom
NOTE: -

NODE: stepP:p7:po-dense
KIND: step
TITLE: (c) All of $\mathcal O$
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-dense@L157-L157
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-dense@L157-L157
CONTRACT_ID: stepP:p7:po-dense
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed data and source premises of bpP:p7:poincare. Earlier proof facts and cited results are supplied through DEPS, not extra hypotheses.
SOURCE_QUANTIFIERS: points of O
SOURCE_CONCLUSION: D Psi^T M_0 D Psi=M_0 on all of O, i.e. Psi is a 1-chart on O and D Psi is invertible
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p7:po-symp, stepP:p7:po-an, I:bpI:p7:x-forms, bpP:p1:omega-algebra, bpP:p7:e-dense, bpP:p1:chart, bpP:p7:conv#data, bpP:p7:poincare-def, bpP:p1:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p7:po-symp | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-dense@L157-L157 | identity on the dense set A
EDGE: stepP:p7:po-an | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-dense@L157-L157 | Psi is C^1 (analytic) on O
EDGE: I:bpI:p7:x-forms | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-dense@L157-L157 | exterior calculus: form identity iff matrix identity
EDGE: bpP:p1:omega-algebra | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-dense@L157-L157 | (b) invertibility and (c) form identity for the linear map
EDGE: bpP:p7:e-dense | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-dense@L157-L157 | continuous identity on a dense subset
EDGE: bpP:p1:chart | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-dense@L157-L157 | chart property with c=1
EDGE: bpP:p7:conv#data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-dense@L157-L157 | frozen order (lambda,xi;Lambda,eta)
EDGE: bpP:p7:poincare-def | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-dense@L157-L157 | uses the domain O and Gamma=(xi^2+eta^2)/2
EDGE: bpP:p1:conv#data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-dense@L157-L157 | the named matrix M_0 is defined in Part 1 conventions, not in the Part 7 conventions
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7+sol-delta-P-i
REVIEWER: sol-delta-P-q
LEAN_STATUS: PROVED
LEAN_REF: poincare_symplectic (KAM/Planetary/Poincare/Symplectic.lean)
LEAN_NOTE: audit P7-2 PASS WITH NOTES; named poincare (c), including Gamma=0
NOTE: -

NODE: stepP:p7:po-el
KIND: step
TITLE: (d) Elements
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-el@L158-L159
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-el@L158-L159
CONTRACT_ID: stepP:p7:po-el
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed data and source premises of bpP:p7:poincare. Earlier proof facts and cited results are supplied through DEPS, not extra hypotheses.
SOURCE_QUANTIFIERS: points of O
SOURCE_CONCLUSION: Psi(O) subset K_{m,kappa}; E=-kappa^2m^3/(2Lambda^2); a=Lambda^2/(m^2 kappa); action Lambda; cr=Lambda k; LRL vector=v
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p7:po-del, bpP:p7:kepler, stepP:p7:po-el#circular, I:bpI:p7:orbit-identities, stepP:p7:po-circ, bpP:p7:kepler-data, bpP:p7:conv#data, bpP:p7:poincare-def
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p7:po-del | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-el@L158-L158 | Psi=Q_{m,kappa} o (...) on A
EDGE: bpP:p7:kepler | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-el@L158-L158 | (b): l(q)=a(1-e cos u), E, cr
EDGE: stepP:p7:po-el#circular | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-el@L158-L158 | scalar circular identities from either explicitly offered derivation
EDGE: I:bpI:p7:orbit-identities | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-el@L158-L158 | orbit identities for P^2, 1/l(Q), Q.P in the orbit frame
EDGE: stepP:p7:po-circ | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-el@L159-L159 | values at xi=eta=0
EDGE: bpP:p7:kepler-data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-el@L158-L158 | K_{m,kappa}, a, action
EDGE: bpP:p7:conv#data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-el@L158-L158 | uses the positive mass/strength, physical-length or rotation conventions of the package
EDGE: bpP:p7:poincare-def | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-el@L158-L158 | O, Psi, k and v used in the element identities
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7+sol-delta-P-i
REVIEWER: sol-delta-P-q
LEAN_STATUS: PROVED
LEAN_REF: poincare_elements (KAM/Planetary/Poincare/Symplectic.lean)
LEAN_NOTE: audit P7-2 PASS WITH NOTES; named poincare (d)
NOTE: -

NODE: stepP:p7:po-bij
KIND: step
TITLE: (e) Bijectivity
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-bij@L160-L162
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-bij@L160-L162
CONTRACT_ID: stepP:p7:po-bij
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed data and source premises of bpP:p7:poincare; w,wprime in O for injectivity; target (q,p) in K for surjectivity. Earlier proof facts and cited results are supplied through DEPS, not extra hypotheses.
SOURCE_QUANTIFIERS: w,w' in O; (q,p) in K_{m,kappa}
SOURCE_CONCLUSION: Psi:O->K_{m,kappa} onto; Psi(w')=Psi(w) iff (xi,Lambda,eta) equal and lambda'-lambda in 2piZ; quotient diffeomorphism with the inverse formulas
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p7:po-el, stepP:p7:po-circ, stepP:p7:po-del, bpP:p7:kepler, I:bpI:p7:chart, bpP:p7:range, stepP:p7:rg-scale, stepP:p7:rg-lagrange, stepP:p7:po-dense, stepP:p7:po-an, bpP:p7:e-ift, bpP:p7:o-facts, bpP:p7:regular-kepler, bpP:p7:kepler-data, bpP:p7:conv#data, bpP:p7:poincare-def
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p7:po-el | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-bij@L160-L160 | Lambda, Gamma are functions of (q,p) via (d)
EDGE: stepP:p7:po-circ | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-bij@L160-L160 | Psi at Gamma=0 by (f)
EDGE: stepP:p7:po-del | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-bij@L160-L160 | (ell,g) as in (b)
EDGE: bpP:p7:kepler | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-bij@L160-L160 | (a) injectivity transported by Q_{m,kappa}
EDGE: I:bpI:p7:chart | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-bij@L160-L160 | injectivity modulo 2pi of Q^I
EDGE: bpP:p7:range | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-bij@L161-L161 | Gamma in [0,Lambda)
EDGE: stepP:p7:rg-scale | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-bij@L161-L161 | scaling to strength one
EDGE: stepP:p7:rg-lagrange | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-bij@L161-L161 | equality case of the Lagrange identity
EDGE: stepP:p7:po-dense | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-bij@L162-L162 | D Psi invertible by (c)
EDGE: stepP:p7:po-an | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-bij@L162-L162 | Psi is real analytic
EDGE: bpP:p7:e-ift | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-bij@L162-L162 | bijective analytic local diffeomorphism is a diffeomorphism
EDGE: bpP:p7:o-facts | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-bij@L160-L160 | (xi,eta)=rho e_g, Gamma=Lambda-C
EDGE: bpP:p7:regular-kepler | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-bij@L162-L162 | lambda=Phi(F,v) in the inverse
EDGE: bpP:p7:kepler-data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-bij@L161-L161 | K_{m,kappa}
EDGE: bpP:p7:conv#data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-bij@L160-L160 | uses the positive mass/strength, physical-length or rotation conventions of the package
EDGE: bpP:p7:poincare-def | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-bij@L160-L160 | the chart domain O, Psi, Gamma and the inverse radicand
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7+sol-delta-P-i
REVIEWER: sol-delta-P-q
LEAN_STATUS: PROVED
LEAN_REF: poincare_eq_iff, poincare_localDiffeo, poincare_image, poincareInv, poincareInv_poincare, poincare_poincareInv (KAM/Planetary/Poincare/Bijective.lean)
LEAN_NOTE: audit P7-3 PASS WITH NOTES; named po-bij
NOTE: -

NODE: stepP:p7:po-circ
KIND: step
TITLE: (f) Circular points
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-circ@L163-L163
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-circ@L163-L163
CONTRACT_ID: stepP:p7:po-circ
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Gamma=0
SOURCE_QUANTIFIERS: lambda, Lambda>0
SOURCE_CONCLUSION: v=0, k=1, F=lambda, J=1, q=a(cos lambda,sin lambda), p=m sqrt(kappa/a)J_0 c (the circular point)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p7:regular-kepler, bpP:p0:circular#circularPoint, bpP:p7:poincare-def, bpP:p7:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p7:regular-kepler | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-circ@L163-L163 | F(lambda,0)=lambda
EDGE: bpP:p0:circular#circularPoint | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-circ@L163-L163 | compare with the circular point
EDGE: bpP:p7:poincare-def | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-circ@L163-L163 | q, p formulas
EDGE: bpP:p7:conv#data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-circ@L163-L163 | uses the positive mass/strength, physical-length or rotation conventions of the package
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7+sol-review-P-i
REVIEWER: sol-delta-P-i
LEAN_STATUS: PROVED
LEAN_REF: poincare_circular (KAM/Planetary/Poincare/Symplectic.lean)
LEAN_NOTE: audit P7-2 PASS WITH NOTES; named poincare (f)
NOTE: -

NODE: bpP:p7:holomorphic
KIND: proposition
TITLE: Holomorphic extension near the circular orbits
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:holomorphic@L166-L170
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:holomorphic@L171-L174
CONTRACT_ID: bpP:p7:holomorphic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Lambda^o>0; N(Lambda^o)={(lambda,xi,Lambda,eta) in C^4: ¦Im lambda¦<1/4, ¦Lambda-Lambda^o¦<Lambda^o/2, ¦xi¦,¦eta¦<sqrt(Lambda^o)/16}; formulas of Definition poincare-def with F of Prop regular-kepler(b)
SOURCE_QUANTIFIERS: Lambda^o>0; then points of N(Lambda^o)
SOURCE_CONCLUSION: the formulas define a holomorphic Psi:N(Lambda^o)->C^4, 2pi-periodic in lambda, real at real points, with N(Lambda^o) cap R^4 subset O and D Psi^T M_0 D Psi=M_0 at real points (hypotheses of Lemma bpP:p1:hol-chart with c=1)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p7:ho-size, stepP:p7:ho-hol, bpP:p7:poincare-def, bpP:p7:regular-kepler
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p7:ho-size | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:holomorphic@L172-L172 | proof step Sizes
EDGE: stepP:p7:ho-hol | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:holomorphic@L173-L173 | proof step Holomorphy
EDGE: bpP:p7:poincare-def | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:holomorphic@L169-L169 | formulas of Psi
EDGE: bpP:p7:regular-kepler | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:holomorphic@L169-L169 | F of (b)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7
REVIEWER: sol-review-P-i
LEAN_STATUS: PROVED
LEAN_REF: poincareGammaC, poincareVC, poincareC, poincareNbhd, poincare_holomorphic (KAM/Planetary/Poincare/Holomorphic.lean); symplecticFormC, symplecticFormC_phaseToC, poincare_fderiv_real_restriction, poincare_holomorphic_symplectic (KAM/Planetary/Poincare/HolomorphicSymplectic.lean)
LEAN_NOTE: audit P7-4 audit-2 PASS WITH NOTES (closes audit-1 F1)
NOTE: the final sentence (hypotheses of Lemma bpP:p1:hol-chart satisfied) is an interface this node supplies to Part 8; no edge to bpP:p1:hol-chart

NODE: stepP:p7:ho-size
KIND: step
TITLE: Sizes
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ho-size@L172-L172
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ho-size@L172-L172
CONTRACT_ID: stepP:p7:ho-size
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (lambda,xi,Lambda,eta) in N(Lambda^o)
SOURCE_QUANTIFIERS: points of N(Lambda^o)
SOURCE_CONCLUSION: Re k>0.99, ¦1+k¦>1.9, radicand has argument <pi/2 so s holomorphic, ¦v_0¦+¦v_1¦<1/4, (lambda,v) in N_0, F holomorphic with ¦J¦>3/5
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: I:bpI:p7:x-hol, bpP:p7:regular-kepler, bpP:p7:poincare-def
ROUTES: -
ROUTE_FOR: -
EDGE: I:bpI:p7:x-hol | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ho-size@L172-L172 | holomorphic calculus and principal square root on Re>0
EDGE: bpP:p7:regular-kepler | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ho-size@L172-L172 | (b): F holomorphic on N_0 with ¦J¦>3/5
EDGE: bpP:p7:poincare-def | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ho-size@L172-L172 | k, v, Gamma
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7
REVIEWER: sol-review-P-i
LEAN_STATUS: PROVED
LEAN_REF: poincare_holomorphic (KAM/Planetary/Poincare/Holomorphic.lean)
LEAN_NOTE: audit P7-4 PASS WITH NOTES; named ho-size
NOTE: -

NODE: stepP:p7:ho-hol
KIND: step
TITLE: Holomorphy, reality, periodicity
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ho-hol@L173-L173
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ho-hol@L173-L173
CONTRACT_ID: stepP:p7:ho-hol
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed data and source premises of bpP:p7:holomorphic; Lambda^o>0, points in N(Lambda^o). Earlier proof facts and cited results are supplied through DEPS, not extra hypotheses.
SOURCE_QUANTIFIERS: points of N(Lambda^o)
SOURCE_CONCLUSION: Psi holomorphic, 2pi-periodic in lambda, real at real points with real points in O; D Psi^T M_0 D Psi=M_0 at real points
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p7:ho-size, I:bpI:p7:x-hol, stepP:p7:po-an, bpP:p7:poincare, K:bp:p1:real-restriction, bpP:p7:poincare-def, bpP:p1:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p7:ho-size | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ho-hol@L173-L173 | sizes and holomorphy of the ingredients
EDGE: I:bpI:p7:x-hol | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ho-hol@L173-L173 | holomorphic calculus
EDGE: stepP:p7:po-an | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ho-hol@L173-L173 | periodicity as in Step (a)
EDGE: bpP:p7:poincare | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ho-hol@L173-L173 | (c): the real matrix identity
EDGE: K:bp:p1:real-restriction | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ho-hol@L173-L173 | complex derivative restricts to the real one
EDGE: bpP:p7:poincare-def | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ho-hol@L173-L173 | the explicit q,p formulas and real domain O
EDGE: bpP:p1:conv#data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:ho-hol@L173-L173 | M_0 in the real-point matrix identity
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7+sol-delta-P-i
REVIEWER: sol-delta-P-q
LEAN_STATUS: PROVED
LEAN_REF: poincare_holomorphic (KAM/Planetary/Poincare/Holomorphic.lean); poincare_fderiv_real_restriction, poincare_holomorphic_symplectic (KAM/Planetary/Poincare/HolomorphicSymplectic.lean)
LEAN_NOTE: audit P7-4 audit-1 + audit-2 PASS WITH NOTES; named ho-hol
NOTE: SOURCE_GAP: L173 applies real derivative restriction on N(Lambda^o), while K:bp:p1:real-restriction is stated for a function on a full torus strip T_rho. N is bounded in Lambda,xi,eta, so that hypothesis is not supplied. The needed local open-domain restriction fact is true but is not the literal cited theorem: supply its local version or a valid localization, without adding it as an assumed premise. The other holomorphy/reality/periodicity and real symplectic-identity dependencies remain as recorded.

NODE: bpP:p7:product-def
KIND: definition
TITLE: Product chart
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:product-def@L190-L192
PROOF_SOURCE: -
CONTRACT_ID: bpP:p7:product-def
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: sec-product#data: n>=1, G,m0>0, kappa=G m0, m in (0,infinity)^n
SOURCE_QUANTIFIERS: n, G, m0, m; then w in Ph_{2n}
SOURCE_CONCLUSION: defines O_n={w: (lambda_i,xi_i,Lambda_i,eta_i) in O for all i}={Lambda_i>0, (xi_i^2+eta_i^2)/2<Lambda_i}, Psi^(n)(w)=(q,p) with (q^(i),p^(i))=Psi_{m_i,kappa}(lambda_i,xi_i,Lambda_i,eta_i), h(Lambda)=-sum kappa^2m_i^3/(2Lambda_i^2), K^(n)={(q,p): (q^(i),p^(i)) in K_{m_i,kappa} for all i}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p7:poincare-def, bpP:p7:kepler-data, bpP:p7:sec-product#data, bpP:p0:body#bodyVector
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p7:poincare-def | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:product-def@L191-L191 | Psi_{m_i,kappa} and O
EDGE: bpP:p7:kepler-data | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:product-def@L191-L191 | K_{m_i,kappa}
EDGE: bpP:p7:sec-product#data | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:product-def@L190-L190 | data and coordinates of the section
EDGE: bpP:p0:body#bodyVector | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:product-def@L191-L191 | q^(i), p^(i) are body blocks
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7
REVIEWER: sol-review-P-i
LEAN_STATUS: PROVED
LEAN_REF: poincareProd, poincareProdDom, hProd, regionProd (KAM/Planetary/Poincare/Product.lean)
LEAN_NOTE: audit P7-5 PASS WITH NOTES
NOTE: the identification K^(n)=ProgradeElliptic (kappa=1) is proved in bpP:p7:d25(d); no edge to the anchor here

NODE: bpP:p7:product-chart
KIND: theorem
TITLE: Product Poincar\'e chart
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:product-chart@L194-L203
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:product-chart@L204-L209
CONTRACT_ID: bpP:p7:product-chart
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: sec-product#data; Definition product-def
SOURCE_QUANTIFIERS: n, G, m0, m; then w in O_n (mu, eps arbitrary in (c))
SOURCE_CONCLUSION: (a) Psi^(n) is a real-analytic 1-chart on O_n (c=1), O_n and Psi^(n) invariant under ((2pi k,0),0), Psi^(n)(w')=Psi^(n)(w) iff w'=w+((2pi k,0),0), onto K^(n), real-analytic diffeomorphism O_n/{(2pi k,0,0,0)}->K^(n); (b) H_Kep o Psi^(n)=h(Lambda), h independent of lambda,xi,eta and of any coupling, d h/d Lambda_i=nu_i=kappa^2m_i^3/Lambda_i^3, d^2h/d Lambda_i^2=-3kappa^2m_i^3/Lambda_i^4!=0, h analytic on {Lambda_i>0}; (c) H_mov^Psi=h+mu f_mov o Psi, H_fix^Psi=h+eps f_fix o Psi on O_n, hat f real analytic on Psi^{-1}(W) and independent of mu, eps, D Psi X_{H^Psi}=X_H o Psi, orbits transfer; (d) on Psi^{-1}(W): dot lambda_i=nu_i+mu partial_{Lambda_i}hat f_mov, dot Lambda_i=-mu partial_{lambda_i}hat f_mov, dot xi_i=mu partial_{eta_i}hat f_mov, dot eta_i=-mu partial_{xi_i}hat f_mov; replace mu hat f_mov by eps hat f_fix for the fixed model
CONSTANT_SCOPE: none (hat f does not depend on mu, eps)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p7:pc-prod, stepP:p7:pc-dec, stepP:p7:pc-share, stepP:p7:pc-eq, bpP:p7:product-def, bpP:p7:sec-product#data, bpP:p1:chart, bpP:p6:split, bpP:p6:domain, bpP:p1:chart-field, bpP:p1:chart-orbit, bpP:p0:movham#movingHamiltonian, bpP:p0:fixham#fixedHamiltonian
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p7:pc-prod | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:product-chart@L205-L205 | proof step Product structure
EDGE: stepP:p7:pc-dec | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:product-chart@L206-L206 | proof step Decoupling
EDGE: stepP:p7:pc-share | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:product-chart@L207-L207 | proof step Shared chart
EDGE: stepP:p7:pc-eq | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:product-chart@L208-L208 | proof step (d)
EDGE: bpP:p7:product-def | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:product-chart@L196-L196 | Psi^(n), O_n, K^(n), h
EDGE: bpP:p7:sec-product#data | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:product-chart@L196-L196 | coordinates w
EDGE: bpP:p1:chart | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:product-chart@L196-L196 | 1-chart (Definition chart, c=1)
EDGE: bpP:p6:split | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:product-chart@L197-L197 | H_Kep, f_mov, f_fix of Lemma split
EDGE: bpP:p6:domain | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:product-chart@L198-L198 | W is open
EDGE: bpP:p1:chart-field | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:product-chart@L200-L200 | D Psi X_{H^Psi}=X_H o Psi
EDGE: bpP:p1:chart-orbit | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:product-chart@L200-L200 | orbits transfer
EDGE: bpP:p0:movham#movingHamiltonian | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:product-chart@L200-L200 | H_mov
EDGE: bpP:p0:fixham#fixedHamiltonian | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:product-chart@L200-L200 | H_fix
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7+sol-review-P-i
REVIEWER: sol-delta-P-i
LEAN_STATUS: PROVED
LEAN_REF: product_chart_full, exists_quotient_bijection, fastLatticeSetoid (KAM/Planetary/Poincare/ChartNodes.lean)
LEAN_NOTE: audit GAP-P7 round 2 PASS WITH NOTES; quotient diffeo given as bijection + local analytic inverses
NOTE: -

NODE: stepP:p7:pc-prod
KIND: step
TITLE: Product structure
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:pc-prod@L205-L205
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:pc-prod@L205-L205
CONTRACT_ID: stepP:p7:pc-prod
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed data and source premises of bpP:p7:product-chart. Earlier proof facts and cited results are supplied through DEPS, not extra hypotheses.
SOURCE_QUANTIFIERS: w in O_n
SOURCE_CONCLUSION: D Psi^(n) block diagonal and symplectic; analyticity, lattice invariance, bijectivity, diffeomorphism and openness of O_n blockwise
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p7:poincare, bpP:p7:product-def, bpP:p0:hamsymp#symplecticForm, bpP:p0:body#bodyVector, bpP:p7:sec-product#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p7:poincare | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:pc-prod@L205-L205 | blockwise (a),(c),(e)
EDGE: bpP:p7:product-def | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:pc-prod@L205-L205 | blocks of Psi^(n)
EDGE: bpP:p0:hamsymp#symplecticForm | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:pc-prod@L205-L205 | Omega=sum dz_2^dz_1
EDGE: bpP:p0:body#bodyVector | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:pc-prod@L205-L205 | finProdFinEquiv index bookkeeping
EDGE: bpP:p7:sec-product#data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:pc-prod@L205-L205 | positions lambda_i,xi_i
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7+sol-review-P-i
REVIEWER: sol-delta-P-i
LEAN_STATUS: PROVED
LEAN_REF: pc_prod (KAM/Planetary/SecularForm/ProductInterface.lean); analyticOnNhd_poincareProd, poincareProd_symplectic, poincareProd_image, poincareProd_eq_iff, poincareProd_localDiffeo (KAM/Planetary/Poincare/Product.lean)
LEAN_NOTE: audit S7-R PASS WITH NOTES; named pc-prod
NOTE: -

NODE: stepP:p7:pc-dec
KIND: step
TITLE: Decoupling
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:pc-dec@L206-L206
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:pc-dec@L206-L206
CONTRACT_ID: stepP:p7:pc-dec
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed data and source premises of bpP:p7:product-chart. Earlier proof facts and cited results are supplied through DEPS, not extra hypotheses.
SOURCE_QUANTIFIERS: w in O_n
SOURCE_CONCLUSION: H_Kep o Psi^(n)=h(Lambda) and the derivatives of h
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p6:kepler-part, bpP:p6:split, bpP:p7:poincare, bpP:p7:product-def, bpP:p7:sec-product#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p6:kepler-part | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:pc-dec@L206-L206 | each summand of H_Kep is E_{m_i,kappa}
EDGE: bpP:p6:split | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:pc-dec@L206-L206 | H_Kep of Lemma split
EDGE: bpP:p7:poincare | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:pc-dec@L206-L206 | (d): E_{m_i,kappa} o Psi=-kappa^2m_i^3/(2Lambda_i^2)
EDGE: bpP:p7:product-def | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:pc-dec@L206-L206 | h
EDGE: bpP:p7:sec-product#data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:pc-dec@L206-L206 | uses the fixed product data and coordinate/body dictionary
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7+sol-review-P-i
REVIEWER: sol-delta-P-i
LEAN_STATUS: PROVED
LEAN_REF: product_chart, pc_dec (KAM/Planetary/SecularForm/ProductInterface.lean); keplerPart_poincareProd, hasDerivAt_nu (KAM/Planetary/Poincare/Product.lean)
LEAN_NOTE: audit S7-R PASS WITH NOTES; named pc-dec (product_chart derivatives of h, pc_dec field transport) with P7-5 keplerPart_poincareProd
NOTE: -

NODE: stepP:p7:pc-share
KIND: step
TITLE: Shared chart
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:pc-share@L207-L207
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:pc-share@L207-L207
CONTRACT_ID: stepP:p7:pc-share
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed data and source premises of bpP:p7:product-chart; mu,eps arbitrary; on O_n for splitting, Psi^{-1}(W) for analytic/field claims. Earlier proof facts and cited results are supplied through DEPS, not extra hypotheses.
SOURCE_QUANTIFIERS: w in O_n; mu, eps
SOURCE_CONCLUSION: H^Psi_mov=h+mu f_mov o Psi, H^Psi_fix=h+eps f_fix o Psi; hat f analytic on the open set Psi^{-1}(W) and independent of mu, eps; field statements
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p6:split, bpP:p6:domain, bpP:p1:ext-comp, stepP:p7:pc-prod, bpP:p1:chart-field, bpP:p1:chart-orbit, bpP:p0:movham#movingHamiltonian, bpP:p0:fixham#fixedHamiltonian, bpP:p7:sec-product#data, bpP:p7:product-def, stepP:p7:pc-dec, bpP:p1:chart
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p6:split | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:pc-share@L207-L207 | H=H_Kep+mu f
EDGE: bpP:p6:domain | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:pc-share@L207-L207 | W open and reduced Hamiltonians smooth on W; the analytic bridge is exposed in NOTE
EDGE: bpP:p1:ext-comp | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:pc-share@L207-L207 | composition of analytic maps is analytic
EDGE: stepP:p7:pc-prod | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:pc-share@L207-L207 | Psi^(n) analytic, continuous
EDGE: bpP:p1:chart-field | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:pc-share@L207-L207 | field statement
EDGE: bpP:p1:chart-orbit | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:pc-share@L207-L207 | orbit statement
EDGE: bpP:p0:movham#movingHamiltonian | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:pc-share@L207-L207 | H_mov
EDGE: bpP:p0:fixham#fixedHamiltonian | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:pc-share@L207-L207 | H_fix
EDGE: bpP:p7:sec-product#data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:pc-share@L207-L207 | uses the fixed product data and coordinate/body dictionary
EDGE: bpP:p7:product-def | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:pc-share@L207-L207 | uses Psi^(n), O_n and h
EDGE: stepP:p7:pc-dec | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:pc-share@L207-L207 | substitutes H_Kep composed with Psi^(n)=h into the splitting
EDGE: bpP:p1:chart | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:pc-share@L207-L207 | H^Psi=c^{-1}(H composed with Psi), specialized to c=1
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7+sol-delta-P-i
REVIEWER: sol-delta-P-q
LEAN_STATUS: PROVED
LEAN_REF: pc_share (KAM/Planetary/SecularForm/ProductInterface.lean); movingHamiltonian_poincareProd, fixedHamiltonian_poincareProd, analyticOnNhd_fMov_poincareProd, analyticOnNhd_fFix_poincareProd (KAM/Planetary/Poincare/Product.lean)
LEAN_NOTE: audit S7-R PASS WITH NOTES; named pc-share, with P7-5 splits
NOTE: SOURCE_GAP: L207 asserts that the proof of bpP:p6:domain also gives real analyticity of f_mov,f_fix on W. Its statement/proof L54-L60 supply C-infinity using smooth square-root/reciprocal facts. A real-analytic positive-root/reciprocal argument for the explicit perturbations is needed before analytic composition; do not assume that missing regularity as a hypothesis. The splitting, openness and smooth field transport remain sourced as recorded.

NODE: stepP:p7:pc-eq
KIND: step
TITLE: (d)
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:pc-eq@L208-L208
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:pc-eq@L208-L208
CONTRACT_ID: stepP:p7:pc-eq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed data and source premises of bpP:p7:product-chart; the model Hamiltonian H_mov^Psi or H_fix^Psi, on Psi^{-1}(W). Earlier proof facts and cited results are supplied through DEPS, not extra hypotheses.
SOURCE_QUANTIFIERS: fixed section data, arbitrary mu,eps, w in Psi^{-1}(W), i<n; G is H_mov^Psi=h+mu hat f_mov or H_fix^Psi=h+eps hat f_fix
SOURCE_CONCLUSION: Hamilton equations in the chart: lambda_i'=nu_i+d_{Lambda_i}(mu f), Lambda_i'=-mu d_{lambda_i}f, xi_i'=mu d_{eta_i}f, eta_i'=-mu d_{xi_i}f for the moving model with f=hat f_mov; for the fixed model replace every mu f by eps hat f_fix
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p0:hamsymp#hamiltonianVectorField, stepP:p7:pc-dec, stepP:p7:pc-share, bpP:p7:sec-product#data, bpP:p1:chart, bpP:p7:product-def
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:hamsymp#hamiltonianVectorField | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:pc-eq@L208-L208 | definition of X_G
EDGE: stepP:p7:pc-dec | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:pc-eq@L208-L208 | nu_i=d h/d Lambda_i
EDGE: stepP:p7:pc-share | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:pc-eq@L208-L208 | H^Psi=h+mu hat f
EDGE: bpP:p7:sec-product#data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:pc-eq@L208-L208 | z_1=(lambda,xi), z_2=(Lambda,eta)
EDGE: bpP:p1:chart | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:pc-eq@L208-L208 | the pulled-back Hamiltonian H^Psi used in the model equations
EDGE: bpP:p7:product-def | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:pc-eq@L208-L208 | Psi^(n), O_n and the h(Lambda) in the model Hamiltonians
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7+sol-delta-P-i
REVIEWER: sol-delta-P-q
LEAN_STATUS: PROVED
LEAN_REF: pc_eq, ChartHamiltonEq (KAM/Planetary/Poincare/ChartNodes.lean)
LEAN_NOTE: audit GAP-P7 round 2 PASS WITH NOTES
NOTE: -

NODE: bpP:p7:tube
KIND: lemma
TITLE: The tube in chart coordinates
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:tube@L215-L217
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:tube@L218-L221
CONTRACT_ID: bpP:p7:tube
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: fixed product data n>=1, G,m0>0, positive m_i, kappa=Gm0; a_i>0 and Lambda_i^*=m_i sqrt(kappa a_i); U_eta denotes the circular tube
SOURCE_QUANTIFIERS: fixed n,G,m0,m,a; for every delta>0 there exists eta_delta>0; for every eta in (0,eta_delta] the inclusion and all preimage bounds hold; the circular identity holds for every phi in R^n
SOURCE_CONCLUSION: U_eta subset K^(n); every w in O_n with Psi^(n)(w) in U_eta satisfies ¦Lambda_i-Lambda_i^*¦<delta and (xi_i^2+eta_i^2)/2<delta for all i; circ(phi)=Psi^(n)((2pi phi,0),(Lambda^*,0))
CONSTANT_SCOPE: eta_delta depends on delta (and on a, m, kappa)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p7:tu-circ, stepP:p7:tu-cont, bpP:p0:circular#circularPoint, bpP:p0:circular#circularTube, bpP:p7:product-def, bpP:p7:sec-product#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p7:tu-circ | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:tube@L219-L219 | proof step Circular points
EDGE: stepP:p7:tu-cont | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:tube@L220-L220 | proof step Continuity of the elements
EDGE: bpP:p0:circular#circularPoint | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:tube@L216-L216 | circ(phi)
EDGE: bpP:p0:circular#circularTube | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:tube@L216-L216 | U_eta
EDGE: bpP:p7:product-def | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:tube@L216-L216 | O_n, Psi^(n), K^(n)
EDGE: bpP:p7:sec-product#data | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:tube@L216-L216 | uses the product data n,G,m0,m and kappa=Gm0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7+sol-review-P-i
REVIEWER: sol-delta-P-i
LEAN_STATUS: PROVED
LEAN_REF: circularPoint_eq_poincareProd, tube_in_chart (KAM/Planetary/Poincare/Tube.lean)
LEAN_NOTE: audit P7-6 PASS WITH NOTES
NOTE: -

NODE: stepP:p7:tu-circ
KIND: step
TITLE: Circular points
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:tu-circ@L219-L219
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:tu-circ@L219-L219
CONTRACT_ID: stepP:p7:tu-circ
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed data and source premises of bpP:p7:tube; a_i>0, Lambda_i^*=m_i sqrt(kappa a_i), phi in R^n. Earlier proof facts and cited results are supplied through DEPS, not extra hypotheses.
SOURCE_QUANTIFIERS: phi in R^n
SOURCE_CONCLUSION: Psi^(n)((2pi phi,0),(Lambda^*,0))=circ(phi)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p7:poincare, bpP:p0:circular#circularPoint, bpP:p7:product-def, bpP:p7:sec-product#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p7:poincare | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:tu-circ@L219-L219 | (f) circular points
EDGE: bpP:p0:circular#circularPoint | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:tu-circ@L219-L219 | circ(phi)
EDGE: bpP:p7:product-def | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:tu-circ@L219-L219 | Psi^(n)
EDGE: bpP:p7:sec-product#data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:tu-circ@L219-L219 | uses the fixed product data and coordinate/body dictionary
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7+sol-review-P-i
REVIEWER: sol-delta-P-i
LEAN_STATUS: PROVED
LEAN_REF: circularPoint_eq_poincareProd (KAM/Planetary/Poincare/Tube.lean)
LEAN_NOTE: audit P7-6 PASS WITH NOTES; named tube
NOTE: -

NODE: stepP:p7:tu-cont
KIND: step
TITLE: Continuity of the elements
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:tu-cont@L220-L220
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:tu-cont@L220-L220
CONTRACT_ID: stepP:p7:tu-cont
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed data and source premises of bpP:p7:tube; a_i>0, delta>0. Earlier proof facts and cited results are supplied through DEPS, not extra hypotheses.
SOURCE_QUANTIFIERS: delta>0
SOURCE_CONCLUSION: there is eta_delta>0 with U_eta subset V_delta subset K^(n) for eta<=eta_delta; preimages have ¦Lambda_i-Lambda_i^*¦<delta and Gamma_i<delta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p7:poincare, stepP:p7:tu-circ, bpP:p7:e-comp, bpP:p0:circular#circularTube, bpP:p0:circular#circularPoint, bpP:p7:product-def, bpP:p7:kepler-data, bpP:p7:sec-product#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p7:poincare | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:tu-cont@L220-L220 | (d): elements of a preimage equal Lambda_i(z), Gamma_i(z)
EDGE: stepP:p7:tu-circ | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:tu-cont@L220-L220 | T lies in V_delta: Lambda_i=Lambda_i^*, Gamma_i=0
EDGE: bpP:p7:e-comp | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:tu-cont@L220-L220 | neighbourhood form for compact K inside open V
EDGE: bpP:p0:circular#circularTube | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:tu-cont@L220-L220 | the neighbourhood set is U_eta
EDGE: bpP:p0:circular#circularPoint | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:tu-cont@L220-L220 | torus T of circular points
EDGE: bpP:p7:product-def | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:tu-cont@L220-L220 | K^(n)
EDGE: bpP:p7:kepler-data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:tu-cont@L220-L220 | E_{m_i,kappa}, cr, Lambda_i(z), Gamma_i(z)
EDGE: bpP:p7:sec-product#data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:tu-cont@L220-L220 | uses the fixed product data and coordinate/body dictionary
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7+sol-review-P-i
REVIEWER: sol-delta-P-i
LEAN_STATUS: PROVED
LEAN_REF: tube_in_chart (KAM/Planetary/Poincare/Tube.lean)
LEAN_NOTE: audit P7-6 PASS WITH NOTES; named tube
NOTE: -

NODE: bpP:p7:lattice
KIND: lemma
TITLE: Lattice compatibility for Part~1
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:lattice@L223-L233
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:lattice@L234-L239
CONTRACT_ID: bpP:p7:lattice
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the physical product-chart data of Part 7 (n>=1, G,m0>0, positive m, kappa=G m0); Psi^(n) and O_n of product-def; Theta_n((phi,psi),(I,R))=((phi,sqrt(2R) sin psi),(I,sqrt(2R) cos psi)) on O_0={I_i>0,0<R_i<I_i}, Phi_n:=Psi^(n) o Theta_n; S_2pi denotes the linear position-scaling map used in (c)
SOURCE_QUANTIFIERS: n >= 1 and the fixed physical product-chart data; lattice invariance for every z in O_0 and k in Z^2n; injectivity modulo the lattice for every z,z prime in O_0 with equal images, then existence of a lattice shift m in Z^2n; (c),(d) on the stated chart domains
SOURCE_CONCLUSION: (a) Theta_n and Phi_n are 1-charts on O_0 and O_0 + iota prime_k = O_0 for iota prime_k = ((2 pi k, 0), 0); (b) Phi_n(z + iota prime_k) = Phi_n(z) and Phi_n(z prime) = Phi_n(z) implies z prime = z + iota prime_m for some m in Z^2n: (Q1) with sigma_k = 0 and (Q2) of bpP:p1:torus-transport in the radian convention; (c) Phi_n^(1) = Phi_n o S_2pi is a 2 pi-chart on S_2pi^{-1}(O_0) with (Q1), (Q2) for iota_k = (k, 0), so Corollary phys-pipeline applies to Phi_n and torus-transport (b) to Phi_n^(1); (d) H^{Phi_n} = H o Psi^(n) o Theta_n = h(I) + mu f^ o Theta_n, the unperturbed part independent of psi, R
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p7:la-polar, stepP:p7:la-inv, stepP:p7:la-per, stepP:p7:la-ham, bpP:p7:product-chart, bpP:p7:product-def, bpP:p1:typical, bpP:p1:torus-transport, bpP:p1:period-convert, bpP:p1:phys-pipeline, bpP:p1:chart
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p7:la-polar | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:lattice@L235-L235 | proof step (a)
EDGE: stepP:p7:la-inv | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:lattice@L236-L236 | proof step (b)
EDGE: stepP:p7:la-per | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:lattice@L237-L237 | proof step (c)
EDGE: stepP:p7:la-ham | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:lattice@L238-L238 | proof step (d)
EDGE: bpP:p7:product-chart | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:lattice@L235-L235 | Psi^(n), O_n
EDGE: bpP:p7:product-def | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:lattice@L224-L226 | the chart Psi^(n) and the set O_n
EDGE: bpP:p1:typical | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:lattice@L226-L226 | Remark typical (1): the polar chart formula
EDGE: bpP:p1:torus-transport | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:lattice@L229-L229 | (Q1)-(Q2) and torus transport (b)
EDGE: bpP:p1:period-convert | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:lattice@L230-L230 | S_2pi and the period-one convention
EDGE: bpP:p1:phys-pipeline | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:lattice@L230-L230 | Corollary phys-pipeline applies to Phi_n
EDGE: bpP:p1:chart | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:lattice@L231-L231 | the pulled-back Hamiltonian H^Phi
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: writer-pfixed-revision+sol-delta-P-ah
REVIEWER: sol-delta-P-bc
LEAN_STATUS: PROVED
LEAN_REF: polarDom, polarMap, polarMap_symplectic, analyticOnNhd_polarMap, polarMap_mapsTo, polarDom_shift, poincareProd_polar_symplectic, poincareProd_polar_lattice, poincareProd_polar_periodOne_symplectic, poincareProd_polar_periodOne_lattice, polar_hamiltonian_split (KAM/Planetary/Poincare/Lattice.lean); SecularSpectrum.lattice (KAM/Planetary/SecularForm/ProductInterface.lean)
LEAN_NOTE: composite of audits P7-6 PASS WITH NOTES + S7-R PASS WITH NOTES (lattice polar quotient cut); (d) as moving-Sun split polar_hamiltonian_split
NOTE: restored by the P-FIXED revision (was EXCLUDED as P-FIXED-only, writer ruling 2026-10-28); consumer stepP:p11:tc-polar (Part 11 L90); source fields filled by sonnet-extract-pfixed

NODE: stepP:p7:la-polar
KIND: step
TITLE: (a) Polar chart
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:la-polar@L235-L235
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:la-polar@L235-L235
CONTRACT_ID: stepP:p7:la-polar
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Theta_n blockwise (psi, R) -> (xi, eta) = sqrt(2R)(sin psi, cos psi); O_n
SOURCE_QUANTIFIERS: R > 0, I_i > 0, 0 < R_i < I_i
SOURCE_CONCLUSION: Theta_n is a 1-chart on O_0 (d eta ^ d xi = dR ^ d psi, real analytic for R > 0, into O_n since Gamma_i = R_i < I_i = Lambda_i, identity on the (phi, I) blocks), and so is Phi_n = Psi^(n) o Theta_n as a composition of 1-charts; Theta_n(O_0) is in O_n
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p1:typical, bpP:p1:chart, bpP:p7:product-def, bpP:p7:product-chart
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p1:typical | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:la-polar@L235-L235 | Remark typical (1),(3): composition of 1-charts and the polar chart
EDGE: bpP:p1:chart | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:la-polar@L235-L235 | definition of a 1-chart
EDGE: bpP:p7:product-def | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:la-polar@L235-L235 | O_n = {Gamma < Lambda}
EDGE: bpP:p7:product-chart | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:la-polar@L235-L235 | Product-chart(a) supplies that Psi^(n) is a 1-chart on O_n, needed in the composition with Theta_n.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: writer-pfixed-revision+sol-review-P-w
REVIEWER: sol-delta-P-ah
LEAN_STATUS: PROVED
LEAN_REF: polarMap_symplectic, analyticOnNhd_polarMap, polarMap_mapsTo (KAM/Planetary/Poincare/Lattice.lean)
LEAN_NOTE: audit P7-6 PASS WITH NOTES; named lattice
NOTE: restored by the P-FIXED revision (was EXCLUDED as P-FIXED-only, writer ruling 2026-10-28); consumer stepP:p11:tc-polar (Part 11 L90); source fields filled by sonnet-extract-pfixed

NODE: stepP:p7:la-inv
KIND: step
TITLE: (b) Invariance
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:la-inv@L236-L236
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:la-inv@L236-L236
CONTRACT_ID: stepP:p7:la-inv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the original lattice setting: the physical product-chart data, Psi^(n), O_n, Theta_n and O_0 as explicitly defined in L223-L226; take z in O_0 and k=(k_phi,k_psi) in Z^2n; for the injectivity implication take z prime in O_0 with Phi_n(z prime)=Phi_n(z); periodicity and the product-chart invariance/injectivity conclusions are supplied by the computation and DEPS
SOURCE_QUANTIFIERS: for the shift identity, z in O_0 and k=(k_phi,k_psi) in Z^2n; for injectivity, z,z prime in O_0 with equal Phi_n images, then existence of m_phi,m_psi in Z^n
SOURCE_CONCLUSION: Theta_n(z + iota prime_k) = Theta_n(z) + ((2 pi k_phi, 0), 0); if Phi_n(z prime) = Phi_n(z) then for some m_phi in Z^n, Theta_n(z prime) = Theta_n(z) + ((2 pi m_phi, 0), 0), so phi prime = phi + 2 pi m_phi, I prime = I and, as R, R prime > 0, R prime = R and psi prime - psi = 2 pi m_psi for some m_psi in Z^n
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p7:product-chart, bpP:p7:product-def
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p7:product-chart | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:la-inv@L236-L236 | invariance of Psi^(n) under 2 pi Z^n-shifts of lambda and injectivity modulo them (a)
EDGE: bpP:p7:product-def | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:la-inv@L236-L236 | defines Psi^(n) and O_n used by the invariance and equal-image argument
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: writer-pfixed-revision+sol-delta-P-ah
REVIEWER: sol-delta-P-bc
LEAN_STATUS: PROVED
LEAN_REF: polarMap_shift, polarMap_eq_shift, poincareProd_polar_lattice (KAM/Planetary/Poincare/Lattice.lean)
LEAN_NOTE: audit P7-6 PASS WITH NOTES; named lattice
NOTE: restored by the P-FIXED revision (was EXCLUDED as P-FIXED-only, writer ruling 2026-10-28); consumer stepP:p11:tc-polar (Part 11 L90); source fields filled by sonnet-extract-pfixed

NODE: stepP:p7:la-per
KIND: step
TITLE: (c) Period one
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:la-per@L237-L237
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:la-per@L237-L237
CONTRACT_ID: stepP:p7:la-per
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the original lattice setting: the physical product-chart data, Theta_n, Phi_n and O_0 of L223-L226; define S_2pi(z_1,z_2)=(2 pi z_1,z_2); chart factors and lattice identities from period-convert and steps (a),(b) are supplied through DEPS, not additional premises
SOURCE_QUANTIFIERS: k in Z^2n
SOURCE_CONCLUSION: Phi_n o S_2pi is a 2 pi-chart (composition), S_2pi^{-1}(O_0) + iota_k = S_2pi^{-1}(O_0 + iota prime_k) = S_2pi^{-1}(O_0), and (Q2) for Phi_n o S_2pi is that of (b) read through S_2pi
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p1:period-convert, bpP:p1:typical, stepP:p7:la-polar, stepP:p7:la-inv
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p1:period-convert | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:la-per@L237-L237 | (a) S_2pi is a 2 pi-chart with the lattice shift
EDGE: bpP:p1:typical | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:la-per@L237-L237 | Remark typical (3): composition of charts
EDGE: stepP:p7:la-polar | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:la-per@L237-L237 | Phi_n is a 1-chart (a)
EDGE: stepP:p7:la-inv | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:la-per@L237-L237 | invariance and injectivity modulo shifts (b)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: writer-pfixed-revision+sol-review-P-w
REVIEWER: sol-delta-P-ah
LEAN_STATUS: PROVED
LEAN_REF: poincareProd_polar_periodOne_symplectic, poincareProd_polar_periodOne_lattice (KAM/Planetary/Poincare/Lattice.lean)
LEAN_NOTE: audit P7-6 PASS WITH NOTES; named lattice
NOTE: restored by the P-FIXED revision (was EXCLUDED as P-FIXED-only, writer ruling 2026-10-28); consumer stepP:p11:tc-polar (Part 11 L90); source fields filled by sonnet-extract-pfixed

NODE: stepP:p7:la-ham
KIND: step
TITLE: (d)
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:la-ham@L238-L238
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:la-ham@L238-L238
CONTRACT_ID: stepP:p7:la-ham
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the original lattice setting: the physical product-chart data, Psi^(n), Theta_n, Phi_n and O_0; H is one of the two physical Hamiltonians of product-chart, with its coupling (written mu in L232); the pull-back uses c=1; the decoupling and perturbation identities are supplied by product-chart, not assumed as additional premises
SOURCE_QUANTIFIERS: z in O_0
SOURCE_CONCLUSION: H^{Phi_n} = H o Psi^(n) o Theta_n = h(I) + mu f^ o Theta_n with I = Lambda; unperturbed part independent of psi, R
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p7:product-chart, bpP:p1:chart, bpP:p7:product-def
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p7:product-chart | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:la-ham@L238-L238 | (b),(c): H o Psi^(n) = h(Lambda) + mu f^
EDGE: bpP:p1:chart | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:la-ham@L238-L238 | 1-chart (c = 1): the pulled-back Hamiltonian is H o Phi_n
EDGE: bpP:p7:product-def | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:la-ham@L238-L238 | defines the product map Psi^(n) and integrable Hamiltonian h used in the pulled-back expression
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: writer-pfixed-revision+sol-delta-P-ah
REVIEWER: sol-delta-P-bc
LEAN_STATUS: PROVED
LEAN_REF: la_ham (KAM/Planetary/Poincare/ChartNodes.lean)
LEAN_NOTE: audit GAP-P7 round 2 PASS WITH NOTES
NOTE: restored by the P-FIXED revision (was EXCLUDED as P-FIXED-only, writer ruling 2026-10-28); consumer stepP:p11:tc-polar (Part 11 L90); source fields filled by sonnet-extract-pfixed

NODE: bpP:p7:d25
KIND: proposition
TITLE: D25 definitions = the chart in the eccentric longitude
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:d25@L247-L258
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:d25@L259-L264
CONTRACT_ID: bpP:p7:d25
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n=2, kappa=1 (G=m0=1), m in (0,infinity)^2, w in O_2, i<2; Lambda_i=fast w_2 i, Gamma_i=secularGamma w i; the Lean functions are total and guarded by Lambda_i>0, Gamma_i<Lambda_i; w=(w_1,w_2) in Phase(2+2) with w_1=(lambda,xi), w_2=(Lambda,eta)
SOURCE_QUANTIFIERS: m; w in O_2; i<2; (b),(c) F in R
SOURCE_CONCLUSION: (a) Gamma_i=(xi_i^2+eta_i^2)/2>=0; secularRoot=k_i=1-Gamma_i/Lambda_i in (0,1]; secularEccVector=v_i of Def poincare-def with l(v_i)^2=1-k_i^2; secularAxis=(Lambda_i/m_i)^2=a_i; (b) keplerMeanLongitude w i = Phi(.,v_i) real-analytic increasing bijection commuting with F->F+2pi, derivative longitudeJacobian=J(F,v_i)>=1-e_i>0; F_i(w) the unique solution of Phi=lambda_i, real analytic on O_2; (c) ellipsePosition, ellipseMomentum at F_i(w) equal Psi_{m_i,1}; ellipsePhase m w (F_1,F_2)=Psi^(2)(w); for arbitrary F the point of the osculating ellipse Psi(Phi(F,v_i),xi_i,Lambda_i,eta_i); (d) ProgradeElliptic m z; keplerEnergy=-m_i^3/(2Lambda_i^2); keplerAxis=a_i; keplerAction=Lambda_i; planeCross=Lambda_i-Gamma_i; keplerEccVector=v_i; conversely every z with ProgradeElliptic is Psi^(2)(w), w unique modulo lambda->lambda+2pi k; (e) for Gamma_i>0: (xi_i,eta_i)=rho_i e_{g_i}, F_i=g_i+u_i, lambda_i=ell_i+g_i
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p7:d25-ab, stepP:p7:d25-c, stepP:p7:d25-d, stepP:p7:d25-e, bpP:p7:poincare-def, bpP:p7:regular-kepler, bpP:p7:product-def, bpP:p7:conv#data, bpP:p0:phase#Phase, bpP:p0:blocks#fast, bpP:p14:sb-conv#secularGamma, bpP:p14:sb-conv#secularRoot, bpP:p14:sb-conv#secularEccVector, bpP:p14:sb-conv#secularAxis, bpP:p14:sb-defs#longitudeJacobian, bpP:p14:sb-defs#ellipsePosition, bpP:p14:sb-defs#ellipseMomentum, bpP:p14:sb-defs#ellipsePhase, bpP:p0:d25-prograde#ProgradeElliptic, bpP:p0:d25-kepler#keplerEnergy, bpP:p0:d25-kepler#keplerAxis, bpP:p0:d25-kepler#keplerAction, bpP:p0:d25-cross#planeCross, bpP:p0:d25-kepler#keplerEccVector
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p7:d25-ab | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:d25@L260-L260 | proof step (a),(b)
EDGE: stepP:p7:d25-c | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:d25@L261-L261 | proof step (c)
EDGE: stepP:p7:d25-d | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:d25@L262-L262 | proof step (d)
EDGE: stepP:p7:d25-e | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:d25@L263-L263 | proof step (e)
EDGE: bpP:p7:poincare-def | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:d25@L250-L250 | v_i, k_i, Psi
EDGE: bpP:p7:regular-kepler | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:d25@L251-L251 | F_i(w), Phi, J
EDGE: bpP:p7:product-def | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:d25@L253-L253 | Psi^(2), O_2
EDGE: bpP:p7:conv#data | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:d25@L248-L248 | conventions (kappa=1)
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:d25@L248-L248 | w in Phase(2+2)
EDGE: bpP:p0:blocks#fast | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:d25@L248-L248 | fast w_2 i
EDGE: bpP:p14:sb-conv#secularGamma | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:d25@L248-L248 | secularGamma
EDGE: bpP:p14:sb-conv#secularRoot | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:d25@L250-L250 | secularRoot
EDGE: bpP:p14:sb-conv#secularEccVector | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:d25@L250-L250 | secularEccVector
EDGE: bpP:p14:sb-conv#secularAxis | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:d25@L250-L250 | secularAxis
EDGE: bpP:p14:sb-defs#longitudeJacobian | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:d25@L251-L251 | longitudeJacobian
EDGE: bpP:p14:sb-defs#ellipsePosition | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:d25@L252-L252 | ellipsePosition
EDGE: bpP:p14:sb-defs#ellipseMomentum | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:d25@L252-L252 | ellipseMomentum
EDGE: bpP:p14:sb-defs#ellipsePhase | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:d25@L253-L253 | ellipsePhase
EDGE: bpP:p0:d25-prograde#ProgradeElliptic | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:d25@L255-L255 | ProgradeElliptic
EDGE: bpP:p0:d25-kepler#keplerEnergy | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:d25@L255-L255 | keplerEnergy
EDGE: bpP:p0:d25-kepler#keplerAxis | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:d25@L255-L255 | keplerAxis
EDGE: bpP:p0:d25-kepler#keplerAction | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:d25@L255-L255 | keplerAction
EDGE: bpP:p0:d25-cross#planeCross | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:d25@L255-L255 | planeCross
EDGE: bpP:p0:d25-kepler#keplerEccVector | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:d25@L255-L255 | keplerEccVector
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7
REVIEWER: sol-review-P-i
LEAN_STATUS: PROVED
LEAN_REF: d25 (KAM/Planetary/Poincare/ChartNodes.lean)
LEAN_NOTE: audit GAP-P7 round 2 PASS WITH NOTES
NOTE: the Lean function keplerMeanLongitude is not an anchor (SPEC): its statement is carried by regular-kepler and the d25-ab step

NODE: stepP:p7:d25-ab
KIND: step
TITLE: (a),(b)
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-ab@L260-L260
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-ab@L260-L260
CONTRACT_ID: stepP:p7:d25-ab
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed data and source premises of bpP:p7:d25. Earlier proof facts and cited results are supplied through DEPS, not extra hypotheses.
SOURCE_QUANTIFIERS: w in O_2; i<2
SOURCE_CONCLUSION: the Lean definitions are Gamma=R(eta,xi), k=1-Gamma/Lambda, v=sqrt((1-Gamma/(2Lambda))/Lambda)(xi,eta), Phi(F,v), J=1-v.(cos F,sin F), a=(Lambda/m)^2; hence (a),(b)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p7:o-facts, bpP:p7:regular-kepler, bpP:p7:poincare-def, bpP:p14:sb-conv#secularGamma, bpP:p14:sb-conv#secularRoot, bpP:p14:sb-conv#secularEccVector, bpP:p14:sb-conv#secularAxis, bpP:p14:sb-defs#longitudeJacobian, bpP:p0:plane#planeDot, bpP:p14:sb-conv#orbitalUnit, bpP:p7:product-def
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p7:o-facts | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-ab@L260-L260 | k in (0,1], l(v)^2=1-k^2
EDGE: bpP:p7:regular-kepler | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-ab@L260-L260 | (a): bijection, Jacobian, F analytic
EDGE: bpP:p7:poincare-def | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-ab@L260-L260 | v, k, Phi
EDGE: bpP:p14:sb-conv#secularGamma | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-ab@L260-L260 | secularGamma
EDGE: bpP:p14:sb-conv#secularRoot | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-ab@L260-L260 | secularRoot
EDGE: bpP:p14:sb-conv#secularEccVector | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-ab@L260-L260 | secularEccVector
EDGE: bpP:p14:sb-conv#secularAxis | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-ab@L260-L260 | secularAxis
EDGE: bpP:p14:sb-defs#longitudeJacobian | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-ab@L260-L260 | longitudeJacobian
EDGE: bpP:p0:plane#planeDot | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-ab@L260-L260 | planeDot
EDGE: bpP:p14:sb-conv#orbitalUnit | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-ab@L260-L260 | orbitalUnit
EDGE: bpP:p7:product-def | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-ab@L260-L260 | uses the O_2 domain and product-chart notation in the statement
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7+sol-review-P-i
REVIEWER: sol-delta-P-i
LEAN_STATUS: PROVED
LEAN_REF: secularGamma_eq, secularRoot_eq, secularEccVector_eq, secularAxis_eq (KAM/Planetary/Poincare/D25.lean); keplerMeanLongitude_eq, longitudeJacobian_eq, keplerJac_ge, keplerPhi_strictMono, keplerPhi_shift, keplerLong_unique, analyticOnNhd_keplerLong (KAM/Kepler/Equation.lean)
LEAN_NOTE: audit P7-7 audit-2 PASS (a) + KEP-2 PASS (b)
NOTE: -

NODE: stepP:p7:d25-c
KIND: step
TITLE: (c)
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-c@L261-L261
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-c@L261-L261
CONTRACT_ID: stepP:p7:d25-c
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ellipsePosition=a(kc-v+(v.c)/(1+k)v), ellipseMomentum=m^2/(Lambda J)(J_0c-(v.c)/(1+k)J_0v), c=orbitalUnit F
SOURCE_QUANTIFIERS: w in O_2; i<2; F in R
SOURCE_CONCLUSION: the Lean ellipse position and momentum are the q,p of Definition poincare-def with kappa=1 and arbitrary F; at F=F_i(w) they equal Psi; for arbitrary F they equal Psi(Phi(F,v_i),xi_i,Lambda_i,eta_i)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p7:poincare-def, stepP:p7:d25-ab, bpP:p7:regular-kepler, bpP:p14:sb-defs#ellipsePosition, bpP:p14:sb-defs#ellipseMomentum, bpP:p14:sb-defs#longitudeJacobian, bpP:p14:sb-conv#orbitalUnit, bpP:p7:product-def, bpP:p14:sb-defs#ellipsePhase
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p7:poincare-def | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-c@L261-L261 | q, p formulas
EDGE: stepP:p7:d25-ab | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-c@L261-L261 | identification of v, k, J, a
EDGE: bpP:p7:regular-kepler | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-c@L261-L261 | uniqueness F=F(lambda',v_i)
EDGE: bpP:p14:sb-defs#ellipsePosition | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-c@L261-L261 | ellipsePosition
EDGE: bpP:p14:sb-defs#ellipseMomentum | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-c@L261-L261 | ellipseMomentum
EDGE: bpP:p14:sb-defs#longitudeJacobian | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-c@L261-L261 | longitudeJacobian
EDGE: bpP:p14:sb-conv#orbitalUnit | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-c@L261-L261 | orbitalUnit
EDGE: bpP:p7:product-def | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-c@L261-L261 | uses the O_2 domain and product-chart notation in the statement
EDGE: bpP:p14:sb-defs#ellipsePhase | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-c@L261-L261 | assembles the component identities into the ellipsePhase identity of clause (c)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7+sol-review-P-i
REVIEWER: sol-delta-P-i
LEAN_STATUS: PROVED
LEAN_REF: poincare_block_eq_ellipse, ellipsePhase_eq_poincareProd, ellipsePhase_eq_poincareProd_self (KAM/Planetary/Poincare/D25.lean)
LEAN_NOTE: audit P7-7 audit-2 PASS; named d25(c)
NOTE: -

NODE: stepP:p7:d25-d
KIND: step
TITLE: (d)
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-d@L262-L262
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-d@L262-L262
CONTRACT_ID: stepP:p7:d25-d
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed data and source premises of bpP:p7:d25; z=Psi^(2)(w) for the forward assertions; ProgradeElliptic(m,z) for the converse. Earlier proof facts and cited results are supplied through DEPS, not extra hypotheses.
SOURCE_QUANTIFIERS: fixed n=2, kappa=1 and m in (0,infinity)^2; forward: every w in O_2 and i<2, z=Psi^(2)(w); converse: every physical z with ProgradeElliptic(m,z), with a preimage w to be obtained
SOURCE_CONCLUSION: ProgradeElliptic m z with the stated values of keplerEnergy, keplerAxis, keplerAction, planeCross, keplerEccVector; converse and uniqueness modulo lambda->lambda+2pi k
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p7:poincare, bpP:p7:product-chart, stepP:p7:d25-ab, bpP:p0:d25-prograde#ProgradeElliptic, bpP:p0:d25-kepler#keplerEnergy, bpP:p0:d25-kepler#keplerAxis, bpP:p0:d25-kepler#keplerAction, bpP:p0:d25-kepler#keplerEccVector, bpP:p0:plane#planeLength, bpP:p7:product-def, bpP:p0:d25-cross#planeCross
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p7:poincare | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-d@L262-L262 | (d): Psi(w) in K_{m_i,1}, E, a, action, LRL=v
EDGE: bpP:p7:product-chart | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-d@L262-L262 | (a): converse and uniqueness
EDGE: stepP:p7:d25-ab | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-d@L262-L262 | Gamma_i, a_i
EDGE: bpP:p0:d25-prograde#ProgradeElliptic | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-d@L262-L262 | ProgradeElliptic
EDGE: bpP:p0:d25-kepler#keplerEnergy | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-d@L262-L262 | keplerEnergy
EDGE: bpP:p0:d25-kepler#keplerAxis | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-d@L262-L262 | keplerAxis
EDGE: bpP:p0:d25-kepler#keplerAction | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-d@L262-L262 | keplerAction
EDGE: bpP:p0:d25-kepler#keplerEccVector | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-d@L262-L262 | keplerEccVector
EDGE: bpP:p0:plane#planeLength | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-d@L262-L262 | planeLength>0
EDGE: bpP:p7:product-def | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-d@L262-L262 | Psi^(2), K^(2)
EDGE: bpP:p0:d25-cross#planeCross | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-d@L262-L262 | the physical angular-momentum identity uses the planar cross product
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7+sol-delta-P-i
REVIEWER: sol-delta-P-q
LEAN_STATUS: PROVED
LEAN_REF: keplerFunctions_poincareProd, exists_poincareProd_of_progradeElliptic (KAM/Planetary/Poincare/D25.lean); poincareProd_eq_iff (KAM/Planetary/Poincare/Product.lean)
LEAN_NOTE: audit P7-7 audit-2 PASS; named d25(d); uniqueness modulo 2pi k via P7-5 poincareProd_eq_iff
NOTE: -

NODE: stepP:p7:d25-e
KIND: step
TITLE: (e)
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-e@L263-L263
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-e@L263-L263
CONTRACT_ID: stepP:p7:d25-e
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed data and source premises of bpP:p7:d25; Gamma_i>0. Earlier proof facts and cited results are supplied through DEPS, not extra hypotheses.
SOURCE_QUANTIFIERS: w in O_2 with Gamma_i>0
SOURCE_CONCLUSION: (xi_i,eta_i)=rho_i e_{g_i}, F_i=g_i+u_i, lambda_i=ell_i+g_i
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p7:po-del, bpP:p7:regular-kepler, bpP:p7:product-def, bpP:p7:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p7:po-del | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-e@L263-L263 | Delaunay correspondence on Gamma>0
EDGE: bpP:p7:regular-kepler | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-e@L263-L263 | (c): F=g+u_R
EDGE: bpP:p7:product-def | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-e@L263-L263 | uses the O_2 domain and product-chart notation in the statement
EDGE: bpP:p7:conv#data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:d25-e@L263-L263 | e_g and the perihelion/mean-longitude rotation convention
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7+sol-delta-P-i
REVIEWER: sol-delta-P-q
LEAN_STATUS: PROVED
LEAN_REF: d25_e, D25Polar (KAM/Planetary/Poincare/ChartNodes.lean)
LEAN_NOTE: audit GAP-P7 round 2 PASS WITH NOTES
NOTE: -

NODE: bpP:p7:conv#data
KIND: definition
TITLE: Conventions of Part 7 (m, kappa, l, angles, Omega, J_0, R(g), e_g, cr, Q^I)
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:conv#data@L27-L33
PROOF_SOURCE: -
CONTRACT_ID: bpP:p7:conv#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m>0 the planet mass; kappa=G m0>0 the strength of the centre; l the planar length (Definition bpP:p0:plane); angles lambda, ell, g, F in radians (period 2pi); phase point z=(z_1,z_2) positions first, Omega=sum dz_{2,i}^dz_{1,i} (Definition bpP:p0:hamsymp); Poincare coordinates (lambda,xi;Lambda,eta) with positions (lambda,xi) and momenta (Lambda,eta)
SOURCE_QUANTIFIERS: m, kappa (fixed in the part; kappa=G m0 with G, m0 the data of Part 6); then points of R^2 x R^2
SOURCE_CONCLUSION: defines J_0 v=(-v_1,v_0) (quarterTurn), R(g) the rotation by g, e_g=(cos g,sin g), cr(q,p)=q_0p_1-q_1p_0 (planeCross), Omega_chart=dLambda^dlambda+deta^dxi, Gamma=(xi^2+eta^2)/2, and the track-I Delaunay map Q^I(ell,g,L,G) (strength one, unit mass) with (Q^I)^*(sum dq_i^dp_i)=dell^dL+dg^dG
CONSTANT_SCOPE: m and kappa are fixed positive data; kappa=G m0 depends on G, m0 only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p0:plane#planeLength, bpP:p0:hamsymp#symplecticForm, bpP:p0:d25-cross#planeCross, I:bpI:p7:orbit-maps, I:bpI:p7:symplectic, bpP:p0:oscaction#oscillatorAction, bpP:p14:sb-conv#quarterTurn
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:plane#planeLength | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:conv#data@L27-L27 | l is planeLength
EDGE: bpP:p0:hamsymp#symplecticForm | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:conv#data@L28-L28 | frozen sign convention Omega=sum dz_2^dz_1
EDGE: bpP:p0:d25-cross#planeCross | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:conv#data@L32-L32 | cr is planeCross
EDGE: I:bpI:p7:orbit-maps | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:conv#data@L33-L33 | Delaunay map Q^I
EDGE: I:bpI:p7:symplectic | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:conv#data@L33-L33 | (Q^I)^*(sum dq^dp)=dell^dL+dg^dG
EDGE: bpP:p0:oscaction#oscillatorAction | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:conv#data@L30-L30 | Gamma=R(eta,xi) explicitly identifies the oscillator action
EDGE: bpP:p14:sb-conv#quarterTurn | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:conv#data@L32-L32 | J_0 v=(-v_1,v_0) explicitly identifies quarterTurn
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7+sol-delta-P-q
REVIEWER: sol-delta-P-ah
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: not closable (DEFS-P2-audit-1): delaunay public carrier is Phase 2 with an explicit Kepler-solver fallback; faithful on deDom only; owner review
NOTE: created from p7:prose-L27-L33 (SPEC section data); consumers: nearly every statement of Part 7

NODE: bpP:p7:sec-product#data
KIND: definition
TITLE: Data of the product chart (n, G, m0, m, coordinates w)
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:sec-product#data@L188-L188
PROOF_SOURCE: -
CONTRACT_ID: bpP:p7:sec-product#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n>=1; G,m0>0 (kappa=G m0); m=(m_i) in (0,infinity)^n
SOURCE_QUANTIFIERS: n; G, m0; m; then w=(w_1,w_2) in Ph_{2n}
SOURCE_CONCLUSION: defines coordinates w=(w_1,w_2) in Ph_{2n} with w_1=(lambda,xi), w_2=(Lambda,eta), lambda,xi,Lambda,eta in R^n (fast block first: the order of assemble with a=b=n); physical points (q,p) in Ph_{2n} with q^(i)=body(q,i)
CONSTANT_SCOPE: none (free data of the section)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p0:blocks#assemble, bpP:p0:phase#Phase, bpP:p0:body#bodyVector
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:blocks#assemble | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:sec-product#data@L188-L188 | fast block first: the order of assemble
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:sec-product#data@L188-L188 | w and (q,p) are points of Ph_{2n}
EDGE: bpP:p0:body#bodyVector | blueprint-P/parts/p7-kepler-poincare.tex#bpP:p7:sec-product#data@L188-L188 | q^(i)=body(q,i)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p7
REVIEWER: sol-review-P-i
LEAN_STATUS: PROVED
LEAN_REF: Phase (KAM/Frozen/Planetary/Defs/Phase.lean); assemble (KAM/Frozen/Planetary/Defs/Assemble.lean); fast (KAM/Frozen/Planetary/Defs/Fast.lean); slow (KAM/Frozen/Planetary/Defs/Slow.lean); bodyVector (KAM/Frozen/Planetary/Defs/BodyVector.lean); planetBlock (KAM/Planetary/Poincare/Product.lean)
LEAN_NOTE: definitions audit DEFS-P2-audit-1 CLOSABLE
NOTE: created from p7:prose-L188-L188 (SPEC section data); consumers: product-def, product-chart and its steps

NODE: stepP:p7:po-el#circular
KIND: step
TITLE: Scalar circular endpoint identities
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-el@L158-L158
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-el@L158-L158
CONTRACT_ID: stepP:p7:po-el#circular
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m,kappa>0; w=(lambda,0,Lambda,0) in O; q,p=Psi_{m,kappa}(w)
SOURCE_QUANTIFIERS: fixed m,kappa>0; every real lambda and Lambda>0
SOURCE_CONCLUSION: q!=0, E_{m,kappa}(q,p)=-kappa^2 m^3/(2Lambda^2), cr(q,p)=Lambda>0, a(q,p)=Lambda^2/(m^2 kappa), and the physical action is Lambda
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p7:kepler-data, bpP:p7:poincare-def, bpP:p7:conv#data
ROUTES: stepP:p7:po-el#circular-scaled, stepP:p7:po-el#circular-direct
ROUTE_FOR: -
EDGE: stepP:p7:po-el#circular-scaled | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-el@L158-L158 | alternative scalar circular derivation explicitly offered at this line
EDGE: stepP:p7:po-el#circular-direct | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-el@L158-L158 | alternative scalar circular derivation explicitly offered at this line
EDGE: bpP:p7:kepler-data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-el@L158-L158 | E, a and the physical action in the common scalar endpoint contract
EDGE: bpP:p7:poincare-def | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-el@L158-L158 | the common hypothesis w in O and q,p=Psi(w)
EDGE: bpP:p7:conv#data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-el@L158-L158 | the common positive mass/strength and planar length/cross-product conventions
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: new+sol-delta-P-i
REVIEWER: sol-delta-P-q
LEAN_STATUS: PROVED
LEAN_REF: po_el_circular (KAM/Planetary/Poincare/ChartNodes.lean)
LEAN_NOTE: audit GAP-P7 round 2 PASS WITH NOTES
NOTE: covers only the scalar circular identities; the parent separately treats the LRL identity at L158-L159

NODE: stepP:p7:po-el#circular-scaled
KIND: route
TITLE: Circular scalars from the scaled track-I endpoint
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-el@L158-L158
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-el@L158-L158
CONTRACT_ID: stepP:p7:po-el#circular-scaled
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m,kappa>0; w=(lambda,0,Lambda,0) in O; q,p=Psi_{m,kappa}(w)
SOURCE_QUANTIFIERS: fixed m,kappa>0; every real lambda and Lambda>0
SOURCE_CONCLUSION: q!=0, E_{m,kappa}(q,p)=-kappa^2 m^3/(2Lambda^2), cr(q,p)=Lambda>0, a(q,p)=Lambda^2/(m^2 kappa), and the physical action is Lambda
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:circular, bpP:p7:kepler-data, bpP:p7:poincare-def, bpP:p7:regular-kepler, bpP:p7:conv#data
ROUTES: -
ROUTE_FOR: stepP:p7:po-el#circular
EDGE: bpI:p7:circular | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-el@L158-L158 | e=0 scalar endpoint identities
EDGE: bpP:p7:kepler-data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-el@L158-L158 | the defining scale S_m,kappa and E,C,a,action formulas transport the circular endpoint by direct algebra
EDGE: bpP:p7:poincare-def | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-el@L158-L158 | chart formulas at the circular point
EDGE: bpP:p7:regular-kepler | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-el@L158-L158 | F(lambda,0)=lambda
EDGE: bpP:p7:conv#data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-el@L158-L158 | positive mass/strength and physical element conventions
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: new+sol-review-P-i
REVIEWER: sol-delta-P-i
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: covers only the scalar circular identities; the parent separately treats the LRL identity at L158-L159

NODE: stepP:p7:po-el#circular-direct
KIND: route
TITLE: Circular scalars checked directly from clause (f)
STATEMENT_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-el@L158-L158
PROOF_SOURCE: blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-el@L158-L158
CONTRACT_ID: stepP:p7:po-el#circular-direct
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m,kappa>0; w=(lambda,0,Lambda,0) in O; q,p=Psi_{m,kappa}(w)
SOURCE_QUANTIFIERS: fixed m,kappa>0; every real lambda and Lambda>0
SOURCE_CONCLUSION: q!=0, E_{m,kappa}(q,p)=-kappa^2 m^3/(2Lambda^2), cr(q,p)=Lambda>0, a(q,p)=Lambda^2/(m^2 kappa), and the physical action is Lambda
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p7:po-circ, bpP:p7:kepler-data, bpP:p7:conv#data, bpP:p7:poincare-def
ROUTES: -
ROUTE_FOR: stepP:p7:po-el#circular
EDGE: stepP:p7:po-circ | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-el@L158-L158 | explicit circular q,p formulas
EDGE: bpP:p7:kepler-data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-el@L158-L158 | definitions of E,C,a and action
EDGE: bpP:p7:conv#data | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-el@L158-L158 | positive mass/strength and physical element conventions
EDGE: bpP:p7:poincare-def | blueprint-P/parts/p7-kepler-poincare.tex#stepP:p7:po-el@L158-L158 | the source domain O and the equality q,p=Psi(w) in the route hypotheses
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: new+sol-delta-P-i
REVIEWER: sol-delta-P-q
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: covers only the scalar circular identities; the parent separately treats the LRL identity at L158-L159

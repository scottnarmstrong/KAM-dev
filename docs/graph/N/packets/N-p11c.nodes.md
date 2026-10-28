NODE: bpN:p11:real-system
KIND: lemma
TITLE: Real extended systems
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:real-system@L7-L13
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:real-system@L14-L18
CONTRACT_ID: bpN:p11:real-system
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: G holomorphic and 1-periodic in theta on D^e_{r,s}, real on W^e_r (finite norm needed only in (c),(d)); 0<rho<=r
SOURCE_QUANTIFIERS: r,s; G; rho; u; g; Lambda
SOURCE_CONCLUSION: (a) G^R in C^infty(W^e_r), 1-periodic in theta, and X^c_{G^R}(y)=X^c_G(y) in R^{2n+2k} (complex partials at the real point), X^c_{G^R} is C^1 and theta-periodic on W^e_r; (b) G^R o y is constant on J for every G-orbit y in W^e_rho on J; (c) for u in O(rho,s)^e of finite norm and y in W^e_rho: ¦u(y)¦<=¦u¦_{rho,s} and sum_j ¦d_{theta_j}u(y)¦<=¦u¦/(e s); (d) if P_Lambda g=g (g in O(rho,s)^e finite norm, Lambda subset Z^n) then Pi_Lambda^perp d_theta g=0 on W^e_rho
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p11:rs-a, stepN:p11:rs-b, stepN:p11:rs-cd, bpN:p11:ext-class, bpN:p11:s-real#data, bpN:p11:wfield, bpN:p4:norm, bpN:p4:domains, bpN:p3:gen-sol, bpN:p7:resonance-data
EDGE: bpN:p4:norm | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:real-system@L14-L18 | direct use of bpN:p4:norm in the statement or proof at this span
EDGE: bpN:p4:domains | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:real-system@L14-L18 | direct use of bpN:p4:domains in the statement or proof at this span
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:real-system@L14-L18 | direct use of bpN:p3:gen-sol in the statement or proof at this span
EDGE: bpN:p7:resonance-data | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:real-system@L14-L18 | direct use of bpN:p7:resonance-data in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p11:rs-a | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:real-system@L15-L15 | proof step (a)
EDGE: stepN:p11:rs-b | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:real-system@L16-L16 | proof step (b)
EDGE: stepN:p11:rs-cd | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:real-system@L17-L17 | proof step (c),(d)
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:real-system@L8-L8 | O^e, D^e_{r,s}
EDGE: bpN:p11:s-real#data | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:real-system@L8-L12 | W^e_r, G^R, G-orbits
EDGE: bpN:p11:wfield | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:real-system@L9-L9 | X^c_G
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-review-N-f
REVIEWER: sol-delta-N-g
LEAN_STATUS: PROVED
LEAN_REF: real_system, real_system_bounds, real_system_resonant (KAM/Nekhoroshev/Partial/RealSystem.lean)
LEAN_NOTE: audit N11-D PASS WITH NOTES; clauses (a)-(d) via the three exports
NOTE: -

NODE: stepN:p11:rs-a
KIND: step
TITLE: (a)
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-a@L15-L15
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-a@L15-L15
CONTRACT_ID: stepN:p11:rs-a
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: G holomorphic on an open set, real at the real points (not the structure of the variables)
SOURCE_QUANTIFIERS: G
SOURCE_CONCLUSION: (a): G^R smooth and periodic, X^c_{G^R}=X^c_G real, C^1, theta-periodic
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p7:real-system, K:bp:p1:hamiltonian-real, bpN:p4:domains, bpN:p11:ext-class, bpN:p11:s-real#data, bpN:p11:wfield
EDGE: bpN:p4:domains | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-a@L15-L15 | direct use of bpN:p4:domains in the statement or proof at this span
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-a@L15-L15 | direct use of bpN:p11:ext-class in the statement or proof at this span
EDGE: bpN:p11:s-real#data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-a@L15-L15 | direct use of bpN:p11:s-real#data in the statement or proof at this span
EDGE: bpN:p11:wfield | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-a@L15-L15 | direct use of bpN:p11:wfield in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p7:real-system | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-a@L15-L15 | Lemma real-system(a),(b),(c) with D^e_{r,s} cap R^{2n+2k}=W^e_r (proof uses only holomorphy and reality)
EDGE: K:bp:p1:hamiltonian-real | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-a@L15-L15 | real part of a holomorphic function is C^infty and its gradient is the real part of the complex gradient
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-review-N-f
REVIEWER: sol-delta-N-g
LEAN_STATUS: PROVED
LEAN_REF: real_system (KAM/Nekhoroshev/Partial/RealSystem.lean)
LEAN_NOTE: audit N11-D PASS WITH NOTES
NOTE: -

NODE: stepN:p11:rs-b
KIND: step
TITLE: (b)
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-b@L16-L16
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-b@L16-L16
CONTRACT_ID: stepN:p11:rs-b
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:real-system; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: t in J
SOURCE_CONCLUSION: d/dt G^R(y(t))=grad G^R(y).Omega_c grad G^R(y)=0 (Omega_c^T=-Omega_c), so G^R o y is constant
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p1:ext-mvt, bpN:p11:wfield, stepN:p11:rs-a, bpN:p11:ext-chain, bpN:p11:s-real#data, bpN:p3:gen-sol
EDGE: bpN:p11:s-real#data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-b@L16-L16 | direct use of bpN:p11:s-real#data in the statement or proof at this span
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-b@L16-L16 | direct package or input used by this proof step
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p1:ext-mvt | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-b@L16-L16 | zero derivative on an interval gives a constant (mean value inequality)
EDGE: bpN:p11:wfield | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-b@L16-L16 | X^c=Omega_c grad and Omega_c^T=-Omega_c
EDGE: stepN:p11:rs-a | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-b@L16-L16 | G^R differentiable with X^c_{G^R}=Omega_c grad G^R
EDGE: bpN:p11:ext-chain | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-b@L16-L16 | chain rule for G^R along the curve
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-review-N-f
REVIEWER: sol-delta-N-g
LEAN_STATUS: PROVED
LEAN_REF: real_system (KAM/Nekhoroshev/Partial/RealSystem.lean)
LEAN_NOTE: audit N11-D PASS WITH NOTES
NOTE: -

NODE: stepN:p11:rs-cd
KIND: step
TITLE: (c),(d)
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-cd@L17-L17
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-cd@L17-L17
CONTRACT_ID: stepN:p11:rs-cd
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u,g as in (c),(d); statements about Fourier coefficients in theta at fixed I-hat
SOURCE_QUANTIFIERS: y
SOURCE_CONCLUSION: (c) and (d) hold on W^e_rho
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p7:theta-derivative, bpN:p7:resonant-gradient, bpN:p11:ext-part4, bpN:p4:norm, bpN:p11:ext-class, bpN:p11:s-real#data, bpN:p7:resonance-data, bpN:p4:sup-weighted
EDGE: bpN:p4:norm | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-cd@L17-L17 | direct use of bpN:p4:norm in the statement or proof at this span
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-cd@L17-L17 | direct use of bpN:p11:ext-class in the statement or proof at this span
EDGE: bpN:p11:s-real#data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-cd@L17-L17 | direct use of bpN:p11:s-real#data in the statement or proof at this span
EDGE: bpN:p7:resonance-data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-cd@L17-L17 | direct use of bpN:p7:resonance-data in the statement or proof at this span
EDGE: bpN:p4:sup-weighted | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-cd@L17-L17 | direct package or input used by this proof step
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p7:theta-derivative | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-cd@L17-L17 | Lemma theta-derivative
EDGE: bpN:p7:resonant-gradient | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-cd@L17-L17 | Lemma resonant-gradient
EDGE: bpN:p11:ext-part4 | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-cd@L17-L17 | both use Lemma ext-part4 only
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-review-N-f
REVIEWER: sol-delta-N-g
LEAN_STATUS: PROVED
LEAN_REF: real_system_bounds, real_system_resonant (KAM/Nekhoroshev/Partial/RealSystem.lean)
LEAN_NOTE: audit N11-D PASS WITH NOTES; (c) bounds, (d) resonant spans
NOTE: -

NODE: bpN:p11:conj
KIND: lemma
TITLE: Conjugation
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:conj@L20-L22
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:conj@L23-L25
CONTRACT_ID: bpN:p11:conj
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: H in O(r,s)^{e,R}, H-tilde in O(r-tilde,s-tilde)^{e,R} (r-tilde<=r, s-tilde<=s in the same extended structure); Psi: D^e_{r-tilde,s-tilde}->D^e_{r,s} holomorphic, real at real points, DPsi Omega_c DPsi^T=Omega_c; H-tilde=H o Psi; y-tilde an H-tilde-orbit in W^e_{r-tilde} on J
SOURCE_QUANTIFIERS: r,s,r-tilde,s-tilde; H,H-tilde,Psi; J; y-tilde
SOURCE_CONCLUSION: Psi o y-tilde is an H-orbit in W^e_r on J
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p11:cj, bpN:p11:ext-class, bpN:p11:s-real#data, bpN:p11:wfield, bpN:p4:norm, bpN:p4:domains, bpN:p3:gen-sol
EDGE: bpN:p4:norm | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:conj@L23-L25 | direct use of bpN:p4:norm in the statement or proof at this span
EDGE: bpN:p4:domains | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:conj@L23-L25 | direct use of bpN:p4:domains in the statement or proof at this span
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:conj@L23-L25 | direct use of bpN:p3:gen-sol in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p11:cj | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:conj@L24-L24 | proof step (chain rule)
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:conj@L21-L22 | O^{e,R}, D^e
EDGE: bpN:p11:s-real#data | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:conj@L21-L21 | H-orbits in W^e
EDGE: bpN:p11:wfield | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:conj@L21-L21 | Omega_c
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-delta-N-g
REVIEWER: sol-delta2-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: reExtMap, ExtConjHyp (KAM/Nekhoroshev/Partial/Setting.lean)
LEAN_NOTE: data only; conjugation lemma not proved
NOTE: -

NODE: stepN:p11:cj
KIND: step
TITLE: Chain rule
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:cj@L24-L24
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:cj@L24-L24
CONTRACT_ID: stepN:p11:cj
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:conj; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: t in J
SOURCE_CONCLUSION: grad H-tilde^R=Y^T grad H^R o Psi, hence d/dt Psi(y-tilde)=Y Omega_c Y^T grad H^R(Psi y-tilde)=X^c_{H^R}(Psi y-tilde); Psi maps W^e_{r-tilde} into W^e_r
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p7:conjugation, bpN:p11:ext-chain, bpN:p11:wfield, bpN:p11:real-system, bpN:p11:ext-class, bpN:p11:s-real#data
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:cj@L24-L24 | direct use of bpN:p11:ext-class in the statement or proof at this span
EDGE: bpN:p11:s-real#data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:cj@L24-L24 | direct use of bpN:p11:s-real#data in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p7:conjugation | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:cj@L24-L24 | as Lemma conjugation
EDGE: bpN:p11:ext-chain | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:cj@L24-L24 | chain rule
EDGE: bpN:p11:wfield | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:cj@L24-L24 | X^c=Omega_c grad, Y Omega_c Y^T=Omega_c
EDGE: bpN:p11:real-system | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:cj@L24-L24 | H^R, H-tilde^R differentiable with the field X^c_{H^R} (Lemma real-system(a))
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-review-N-f
REVIEWER: sol-delta-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpN:p11:preimage
KIND: lemma
TITLE: Real preimages of a near-identity map
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:preimage@L27-L29
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:preimage@L30-L32
CONTRACT_ID: bpN:p11:preimage
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Psi: D^e_{r-tilde,s-tilde}->C^{2n+2k} holomorphic, real at real points; G=Psi-id with ¦G_theta¦<=d_theta, ¦G_I¦<=d_I, ¦G_{x-tilde}¦<=d_x on D^e_{r-tilde,s-tilde}; 0<rho'<=r-tilde, 0<sigma'<=2 s-tilde; kappa_*=max(d_theta/sigma',d_I/rho',d_x/rho')<=1/4
SOURCE_QUANTIFIERS: r-tilde,s-tilde,rho',sigma'; Psi; d_theta,d_I,d_x
SOURCE_CONCLUSION: every y=(theta_y,I_c,x-tilde_y), theta_y in R^n, x-tilde_y in S-tilde equals Psi(x) for some x in W^e_{r-tilde} with ¦theta_x-theta_y¦<=d_theta, ¦I_x-I_c¦<=d_I, ¦x-tilde_x-x-tilde_y¦<=d_x
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p7:preimage, bpN:p4:general-cauchy, bpN:p11:ext-part4, K:bp:p1:ext-mvt, bpN:p7:ext-banach, bpN:p11:ext-class, bpN:p11:s-real#data, bpN:p11:s-ext-class#data, bpN:p4:domains, bpN:p11:scaled
EDGE: bpN:p4:domains | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:preimage@L30-L32 | direct use of bpN:p4:domains in the statement or proof at this span
EDGE: bpN:p11:scaled | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:preimage@L30-L32 | direct package or input used by this proof step
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p7:preimage | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:preimage@L31-L31 | proof of Lemma preimage with nu(a,b,xi)=max(¦a¦/sigma',¦b¦/rho',¦xi¦/rho') (same contraction argument, conclusion transferred)
EDGE: bpN:p4:general-cauchy | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:preimage@L31-L31 | Cauchy estimate ¦DG¦_nu<=2 kappa_*<=1/2 on the nu-ball
EDGE: bpN:p11:ext-part4 | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:preimage@L31-L31 | Lemma general-cauchy for the extended class
EDGE: K:bp:p1:ext-mvt | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:preimage@L31-L31 | T is a contraction on the convex set X (mean value inequality)
EDGE: bpN:p7:ext-banach | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:preimage@L31-L31 | Banach fixed point theorem
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:preimage@L28-L28 | D^e_{r-tilde,s-tilde}, W^e_{r-tilde}
EDGE: bpN:p11:s-real#data | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:preimage@L28-L28 | W^e_{r-tilde}, S-tilde, real points
EDGE: bpN:p11:s-ext-class#data | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:preimage@L28-L28 | S-tilde and I_c
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-delta-N-g
REVIEWER: sol-delta2-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpN:p11:continuation
KIND: lemma
TITLE: Continuation with independent periodic and transverse coordinates
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:continuation@L35-L37
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:continuation@L38-L41
CONTRACT_ID: bpN:p11:continuation
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E=R^n x R^N (max norm), U subset R^N open, W=R^n x U, F: W->E of class C^1 with F(theta+l,v)=F(theta,v) (l in Z^n), x_0 in W; (T_-,T_+) and z=(z_theta,z_v) the maximal interval and solution; K subset U compact with z_v(t) in K for t in [t_*,T_+), some t_* in [0,T_+)
SOURCE_QUANTIFIERS: n,N; U; F; x_0; K; t_*
SOURCE_CONCLUSION: T_+=+infinity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p11:ct-data, stepN:p11:ct-concl, bpN:p3:gen-maximal, bpN:p3:gen-sol
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p11:ct-data | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:continuation@L39-L39 | proof step (uniform data)
EDGE: stepN:p11:ct-concl | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:continuation@L40-L40 | proof step (conclusion)
EDGE: bpN:p3:gen-maximal | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:continuation@L36-L36 | the maximal interval and solution (Theorem gen-maximal)
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:continuation@L36-L36 | solutions as IsSolIn F W J z
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c
REVIEWER: sol-review-N-f
LEAN_STATUS: PROVED
LEAN_REF: continuation (KAM/Nekhoroshev/Partial/Continuation.lean)
LEAN_NOTE: audit N11-D PASS WITH NOTES
NOTE: -

NODE: stepN:p11:ct-data
KIND: step
TITLE: Uniform data
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ct-data@L39-L39
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ct-data@L39-L39
CONTRACT_ID: stepN:p11:ct-data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:continuation; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: x=(theta,v)
SOURCE_CONCLUSION: Phi=R^n x K has uniform data (delta,M,L): for x with v in K, B-bar(x,delta) subset W, F bounded by M and L-Lipschitz there (M,L the bound and Lipschitz constant of F on C)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p3:uc-delta, bpN:p3:gen-lip, bpN:p3:gen-uniform, bpN:p3:ext-compact
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p3:uc-delta | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ct-data@L39-L39 | choice of delta with K_delta subset U
EDGE: bpN:p3:gen-lip | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ct-data@L39-L39 | bound M and Lipschitz constant L of F on the compact C
EDGE: bpN:p3:gen-uniform | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ct-data@L39-L39 | the notion of uniform data (delta,M,L) being verified
EDGE: bpN:p3:ext-compact | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ct-data@L39-L39 | compactness of the finite product C=[-1,2]^n x K_delta used before gen-lip
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-delta-N-g
REVIEWER: sol-delta2-N-g
LEAN_STATUS: PROVED
LEAN_REF: uniform_data_periodic (KAM/Nekhoroshev/Partial/Continuation.lean)
LEAN_NOTE: audit N11-D PASS WITH NOTES; private helper
NOTE: -

NODE: stepN:p11:ct-concl
KIND: step
TITLE: Conclusion
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ct-concl@L40-L40
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ct-concl@L40-L40
CONTRACT_ID: stepN:p11:ct-concl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:continuation; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: T_+
SOURCE_CONCLUSION: T_+=infinity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:gen-continuation, stepN:p11:ct-data, bpN:p3:gen-uniform
EDGE: bpN:p3:gen-uniform | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ct-concl@L40-L40 | direct package or input used by this proof step
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:gen-continuation | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ct-concl@L40-L40 | Theorem gen-continuation
EDGE: stepN:p11:ct-data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ct-concl@L40-L40 | Phi has uniform data (delta,M,L)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-review-N-f
REVIEWER: sol-delta-N-g
LEAN_STATUS: PROVED
LEAN_REF: continuation (KAM/Nekhoroshev/Partial/Continuation.lean)
LEAN_NOTE: audit N11-D PASS WITH NOTES
NOTE: -

NODE: bpN:p11:transfer
KIND: lemma
TITLE: Stopped transfer through a symplectic map
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:transfer@L43-L52
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:transfer@L53-L61
CONTRACT_ID: bpN:p11:transfer
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: H,H-tilde,Psi as in Lemma conj; ¦.¦_*>=¦.¦ a norm on R^n; (T1) ¦Pi_I Psi(x)-I_x¦_*<=d_* and ¦Pi_{x-tilde}Psi(x)-x-tilde_x¦_inf<=d_x for x in W^e_{r-tilde}, d_x<r-tilde; (T2) every y=(theta_y,I_c,x-tilde_y) (x-tilde_y in S-tilde) is Psi(x), x in W^e_{r-tilde}, ¦I_x-I_c¦_*<=d_*; (T3) (conditional helper, never a premise of the frozen theorem) rho>0 with d_*+rho<r-tilde and T in (0,inf] such that every H-tilde-orbit y-tilde in W^e_{r-tilde} on J-tilde containing 0 with ¦I-tilde(0)-I_c¦_*<=d_* and dist_inf(x-tilde(t),S-tilde)<=d_x on J-tilde satisfies ¦I-tilde(t)-I-tilde(0)¦_*<=rho for t in J-tilde, ¦t¦<=T; F any function with F=X^c_{H^R} on W^e_r; J an interval containing 0; y:R->R^{2n+2k} two-sidedly differentiable with y'=F(y) on J, y(0)=(theta_0,I_c,x-tilde_0), x-tilde_0 in S-tilde; t_1 in J, ¦t_1¦<=T, x-tilde(u) in S-tilde between 0 and t_1
SOURCE_QUANTIFIERS: r,s,r-tilde,s-tilde; H,H-tilde,Psi; norm; d_*,d_x; rho,T; F; J; y; t_1
SOURCE_CONCLUSION: y(u) in W^e_r and ¦I(u)-I_c¦_*<=rho+2 d_* for all u between 0 and t_1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p11:tr-orbit, stepN:p11:tr-E, stepN:p11:tr-bounds, stepN:p11:tr-open, stepN:p11:tr-closed, stepN:p11:tr-concl, bpN:p11:conj, bpN:p11:s-real#data, bpN:p11:ext-class, bpN:p3:gen-symmetry, bpN:p11:wfield, bpN:p11:s-ext-class#data, bpN:p3:gen-sol
EDGE: bpN:p11:wfield | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:transfer@L53-L61 | direct use of bpN:p11:wfield in the statement or proof at this span
EDGE: bpN:p11:s-ext-class#data | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:transfer@L53-L61 | direct use of bpN:p11:s-ext-class#data in the statement or proof at this span
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:transfer@L53-L61 | direct use of bpN:p3:gen-sol in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p11:tr-orbit | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:transfer@L55-L55 | proof step (a normal-form orbit)
EDGE: stepN:p11:tr-E | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:transfer@L56-L56 | proof step (the good set)
EDGE: stepN:p11:tr-bounds | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:transfer@L57-L57 | proof step (bounds on every prefix)
EDGE: stepN:p11:tr-open | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:transfer@L58-L58 | proof step (E open)
EDGE: stepN:p11:tr-closed | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:transfer@L59-L59 | proof step (E closed)
EDGE: stepN:p11:tr-concl | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:transfer@L60-L60 | proof step (conclusion)
EDGE: bpN:p11:conj | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:transfer@L44-L44 | H,H-tilde,Psi as in Lemma conj
EDGE: bpN:p11:s-real#data | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:transfer@L43-L52 | W^e, orbits, S-tilde
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:transfer@L44-L44 | O^{e,R}, D^e
EDGE: bpN:p3:gen-symmetry | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:transfer@L54-L54 | t_1<0 reduced to t_1>0 by time reversal y(-u), -H, -H-tilde
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-delta-N-g
REVIEWER: sol-delta2-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: dropped candidate edges bpN:p7:transfer and bpN:p7:stopped-extension (\source: provenance; the extended argument is proved by its own steps). (T3) is a conditional helper hypothesis, discharged at the consumers by stepN:p11:nr-t3 and stepN:p11:rs-t3

NODE: stepN:p11:tr-orbit
KIND: step
TITLE: A normal-form orbit
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-orbit@L55-L55
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-orbit@L55-L55
CONTRACT_ID: stepN:p11:tr-orbit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (T2); t_1>0
SOURCE_QUANTIFIERS: x; (T_-,T_+)
SOURCE_CONCLUSION: by (T2) choose x in W^e_{r-tilde}; y-tilde is the maximal H-tilde-orbit in W^e_{r-tilde} through x on (T_-,T_+) containing 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:real-system, bpN:p3:gen-maximal, bpN:p11:ext-class, bpN:p11:s-real#data, bpN:p3:gen-sol
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-orbit@L55-L55 | direct use of bpN:p11:ext-class in the statement or proof at this span
EDGE: bpN:p11:s-real#data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-orbit@L55-L55 | direct use of bpN:p11:s-real#data in the statement or proof at this span
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-orbit@L55-L55 | direct use of bpN:p3:gen-sol in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:real-system | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-orbit@L55-L55 | H-tilde^R has a C^1 field on W^e (Lemma real-system(a))
EDGE: bpN:p3:gen-maximal | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-orbit@L55-L55 | maximal solution and interval
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-review-N-f
REVIEWER: sol-delta-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p11:tr-E
KIND: step
TITLE: The good set
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-E@L56-L56
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-E@L56-L56
CONTRACT_ID: stepN:p11:tr-E
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:transfer; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: tau
SOURCE_CONCLUSION: E={tau in [0,t_1]: [0,tau] subset (T_-,T_+), y([0,tau]) subset W^e_r, y=Psi o y-tilde on [0,tau]} contains 0 and is downward closed, hence an interval
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p11:tr-orbit, bpN:p11:ext-class, bpN:p11:s-real#data
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-E@L56-L56 | direct use of bpN:p11:ext-class in the statement or proof at this span
EDGE: bpN:p11:s-real#data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-E@L56-L56 | direct use of bpN:p11:s-real#data in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p11:tr-orbit | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-E@L56-L56 | (T_-,T_+) and y-tilde
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-review-N-f
REVIEWER: sol-delta-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p11:tr-bounds
KIND: step
TITLE: Bounds on every prefix
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-bounds@L57-L57
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-bounds@L57-L57
CONTRACT_ID: stepN:p11:tr-bounds
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: tau in E, u in [0,tau]; (T1),(T3)
SOURCE_QUANTIFIERS: tau,u
SOURCE_CONCLUSION: dist(x-tilde_{y-tilde}(u),S-tilde)<=d_x by (T1); by (T3) ¦I-tilde(u)-I-tilde(0)¦_*<=rho, so ¦I-tilde(u)-I_c¦<=rho+d_*<r-tilde
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p11:tr-E, stepN:p11:tr-orbit, bpN:p11:ext-class, bpN:p11:s-ext-class#data, bpN:p11:s-real#data
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-bounds@L57-L57 | direct use of bpN:p11:ext-class in the statement or proof at this span
EDGE: bpN:p11:s-ext-class#data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-bounds@L57-L57 | direct use of bpN:p11:s-ext-class#data in the statement or proof at this span
EDGE: bpN:p11:s-real#data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-bounds@L57-L57 | direct package or input used by this proof step
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p11:tr-E | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-bounds@L57-L57 | the set E and y=Psi o y-tilde on [0,tau]
EDGE: stepN:p11:tr-orbit | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-bounds@L57-L57 | the orbit y-tilde and its initial value
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-review-N-f
REVIEWER: sol-delta-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p11:tr-open
KIND: step
TITLE: $E$ is open in $[0,t_1]$
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-open@L58-L58
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-open@L58-L58
CONTRACT_ID: stepN:p11:tr-open
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: tau in E, tau<t_1
SOURCE_QUANTIFIERS: tau
SOURCE_CONCLUSION: [tau,tau+epsilon) subset E
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:conj, bpN:p3:gen-uniqueness, bpN:p11:real-system, stepN:p11:tr-E, stepN:p11:tr-orbit, bpN:p11:ext-class, bpN:p11:wfield, bpN:p11:s-real#data, bpN:p3:gen-sol
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-open@L58-L58 | direct use of bpN:p11:ext-class in the statement or proof at this span
EDGE: bpN:p11:wfield | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-open@L58-L58 | direct use of bpN:p11:wfield in the statement or proof at this span
EDGE: bpN:p11:s-real#data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-open@L58-L58 | direct use of bpN:p11:s-real#data in the statement or proof at this span
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-open@L58-L58 | direct use of bpN:p3:gen-sol in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:conj | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-open@L58-L58 | Psi o y-tilde is an H-orbit in W^e_r on (T_-,T_+)
EDGE: bpN:p3:gen-uniqueness | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-open@L58-L58 | y and Psi o y-tilde solve the same equation with the same value at tau (local uniqueness)
EDGE: bpN:p11:real-system | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-open@L58-L58 | F=X^c_{H^R} is C^1 on W^e_r
EDGE: stepN:p11:tr-E | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-open@L58-L58 | definition of E
EDGE: stepN:p11:tr-orbit | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-open@L58-L58 | (T_-,T_+)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-review-N-f
REVIEWER: sol-delta-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p11:tr-closed
KIND: step
TITLE: $E$ is closed
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-closed@L59-L59
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-closed@L59-L59
CONTRACT_ID: stepN:p11:tr-closed
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:transfer; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: tau*
SOURCE_CONCLUSION: the transverse part v=(I-tilde,x-tilde) of y-tilde stays in a compact K subset U; by Lemma continuation T_+>tau*; by continuity tau* in E
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p11:tr-bounds, bpN:p11:continuation, bpN:p11:real-system, stepN:p11:tr-E, stepN:p11:tr-orbit, bpN:p11:ext-class, bpN:p11:wfield, bpN:p11:s-ext-class#data, bpN:p11:s-real#data, bpN:p3:ext-compact
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-closed@L59-L59 | direct use of bpN:p11:ext-class in the statement or proof at this span
EDGE: bpN:p11:wfield | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-closed@L59-L59 | direct use of bpN:p11:wfield in the statement or proof at this span
EDGE: bpN:p11:s-ext-class#data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-closed@L59-L59 | direct use of bpN:p11:s-ext-class#data in the statement or proof at this span
EDGE: bpN:p11:s-real#data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-closed@L59-L59 | direct use of bpN:p11:s-real#data in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p11:tr-bounds | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-closed@L59-L59 | bounds on every prefix [0,tau], tau<tau*
EDGE: bpN:p11:continuation | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-closed@L59-L59 | if T_+=tau* then T_+=infinity (contradiction)
EDGE: bpN:p11:real-system | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-closed@L59-L59 | the field X^c_{H-tilde^R} is C^1 and theta-periodic on R^n x U
EDGE: stepN:p11:tr-E | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-closed@L59-L59 | E, sup E
EDGE: stepN:p11:tr-orbit | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-closed@L59-L59 | (T_-,T_+)
EDGE: bpN:p3:ext-compact | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-closed@L59-L59 | continuous image x-tilde([0,t_1]), its closed bounded d_x-neighbourhood, and the resulting compact transverse product K
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-delta-N-g
REVIEWER: sol-delta2-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p11:tr-concl
KIND: step
TITLE: Conclusion
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-concl@L60-L60
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-concl@L60-L60
CONTRACT_ID: stepN:p11:tr-concl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:transfer; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: u
SOURCE_CONCLUSION: E=[0,t_1] and ¦I(u)-I_c¦_*<=d_*+rho+d_* by (T1), (T3) and (T2)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p11:tr-open, stepN:p11:tr-closed, stepN:p11:tr-E, stepN:p11:tr-bounds, bpN:p11:s-ext-class#data
EDGE: bpN:p11:s-ext-class#data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-concl@L60-L60 | direct use of bpN:p11:s-ext-class#data in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p11:tr-open | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-concl@L60-L60 | E open
EDGE: stepN:p11:tr-closed | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-concl@L60-L60 | E closed
EDGE: stepN:p11:tr-E | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-concl@L60-L60 | E an interval containing 0
EDGE: stepN:p11:tr-bounds | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:tr-concl@L60-L60 | ¦I-tilde(u)-I-tilde(0)¦_*<=rho
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-review-N-f
REVIEWER: sol-delta-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpN:p11:nonresonant
KIND: proposition
TITLE: Nonresonant stability in the extended phase space
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:nonresonant@L65-L68
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:nonresonant@L69-L74
CONTRACT_ID: bpN:p11:nonresonant
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: r,s,K_a,alpha>0, L>=0, p>1, q=p/(p-1), kappa=2 pi K_a s>=6; r=r_B; h holomorphic on V_r(I_c), real on real points; ¦k.omega(I_c)¦>=alpha for 0<¦k¦_1<=K_a (cond-nr, Lambda={0}), cond-L with L, K_a L r<=alpha/p; (SL); f in O(r,s)^{e,R}, ¦f¦<=eps with eps>0, eps<=alpha r/(2^7 q K_a); H=h+f; T_nr=(s r/(5 eps))e^{kappa/6}
SOURCE_QUANTIFIERS: r,s,K_a,alpha,L,p; h; f; eps; F; J; y; t_1
SOURCE_CONCLUSION: for every F with F=X^c_{H^R} on W^e_r, J containing 0, y with y'=F(y) on J, y(0)=(theta_0,I_c,x-tilde_0), x-tilde_0 in S-tilde, and t_1 in J with ¦t_1¦<=T_nr and x-tilde(u) in S-tilde between 0 and t_1: ¦I(u)-I_c¦<=r/2 between 0 and t_1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p11:nr-nf, stepN:p11:nr-t12, stepN:p11:nr-t3, stepN:p11:nr-concl, bpN:p6:setting, bpN:p6#data, bpN:p11:s-nf#data, bpN:p11:ext-class, bpN:p11:s-real#data, bpN:p11:s-ext-class#data, bpN:p4:norm, bpN:p4:domains, bpN:p11:wfield, bpN:p3:gen-sol
EDGE: bpN:p4:norm | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:nonresonant@L69-L74 | direct use of bpN:p4:norm in the statement or proof at this span
EDGE: bpN:p4:domains | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:nonresonant@L69-L74 | direct use of bpN:p4:domains in the statement or proof at this span
EDGE: bpN:p11:wfield | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:nonresonant@L69-L74 | direct use of bpN:p11:wfield in the statement or proof at this span
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:nonresonant@L69-L74 | direct use of bpN:p3:gen-sol in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p11:nr-nf | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:nonresonant@L70-L70 | proof step (normal form)
EDGE: stepN:p11:nr-t12 | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:nonresonant@L71-L71 | proof step ((T1),(T2))
EDGE: stepN:p11:nr-t3 | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:nonresonant@L72-L72 | proof step ((T3))
EDGE: stepN:p11:nr-concl | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:nonresonant@L73-L73 | proof step (transfer)
EDGE: bpN:p6:setting | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:nonresonant@L66-L66 | conditions cond-nr, cond-L
EDGE: bpN:p6#data | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:nonresonant@L66-L66 | K_a, q, kappa
EDGE: bpN:p11:s-nf#data | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:nonresonant@L65-L66 | dictionary h on V_r(I_c), omega, K_a
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:nonresonant@L66-L67 | O^{e,R}, (SL)
EDGE: bpN:p11:s-real#data | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:nonresonant@L66-L66 | W^e_r, S-tilde, orbits
EDGE: bpN:p11:s-ext-class#data | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:nonresonant@L66-L66 | r=r_B, c, lambda
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-delta-N-g
REVIEWER: sol-delta2-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: dropped candidate edge bpN:p7:nonresonant (\source: provenance; the extended proposition is proved by its own steps)

NODE: stepN:p11:nr-nf
KIND: step
TITLE: Normal form
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:nr-nf@L70-L70
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:nr-nf@L70-L70
CONTRACT_ID: stepN:p11:nr-nf
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:nonresonant; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: f
SOURCE_CONCLUSION: Psi: D^e_{r/2,s/6}->D^e_{r,s}, H o Psi=h+g+f_*, eta=¦f_*¦<=e^{-kappa/6}eps, d_I=q K_a eps/alpha<=r/2^7, d_x=r/2^10, d_theta=10 q eps/(2 pi alpha r)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:nf, bpN:p4:norm, bpN:p4:domains, bpN:p11:ext-class, bpN:p11:s-nf#data
EDGE: bpN:p4:norm | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:nr-nf@L70-L70 | direct use of bpN:p4:norm in the statement or proof at this span
EDGE: bpN:p4:domains | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:nr-nf@L70-L70 | direct use of bpN:p4:domains in the statement or proof at this span
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:nr-nf@L70-L70 | direct use of bpN:p11:ext-class in the statement or proof at this span
EDGE: bpN:p11:s-nf#data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:nr-nf@L70-L70 | direct use of bpN:p11:s-nf#data in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:nf | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:nr-nf@L70-L70 | Theorem nf (Lambda={0}) and its conclusions (a)-(c)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-review-N-f
REVIEWER: sol-delta-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p11:nr-t12
KIND: step
TITLE: (T1), (T2)
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:nr-t12@L71-L71
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:nr-t12@L71-L71
CONTRACT_ID: stepN:p11:nr-t12
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:nonresonant; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: x
SOURCE_CONCLUSION: (T1) with d_x<r-tilde; (T2) by Lemma preimage with rho'=r/2, sigma'=s/3: d_I/rho'<=1/64, d_x/rho'<=2^{-9}, d_theta/sigma'<=30/(2^7 kappa)<=30/768<1/4; the preimage has ¦I_x-I_c¦<=d_I=d_*
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:preimage, stepN:p11:nr-nf, bpN:p11:s-nf#data
EDGE: bpN:p11:s-nf#data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:nr-t12@L71-L71 | direct use of bpN:p11:s-nf#data in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:preimage | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:nr-t12@L71-L71 | Lemma preimage with rho'=r/2, sigma'=s/3
EDGE: stepN:p11:nr-nf | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:nr-t12@L71-L71 | the displacement bounds d_I,d_x,d_theta of Theorem nf(c)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-review-N-f
REVIEWER: sol-delta-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p11:nr-t3
KIND: step
TITLE: (T3)
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:nr-t3@L72-L72
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:nr-t3@L72-L72
CONTRACT_ID: stepN:p11:nr-t3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:nonresonant; for the contradiction argument, choose an orbit violating the proposed radius bound; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: y-tilde
SOURCE_CONCLUSION: (T3) with T=T_nr and rho=15r/32 (d_*+rho<r-tilde): if an orbit violated the claim, Lemma exit-ball gives t* with ¦I-tilde(t*)-I-tilde(0)¦=rho and I-tilde in the closed rho-ball before; there ¦dot I-tilde¦<=6 eta/(e s), so rho<=(6/(5e)) r<0.442 r<rho, a contradiction
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p7:exit-ball, bpN:p11:real-system, stepN:p11:nr-nf, bpN:p11:ext-num, bpN:p11:wfield, bpN:p11:ext-class, bpN:p11:s-real#data, bpN:p3:gen-sol, bpN:p11:s-nf#data, K:bp:p1:ext-integral
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:nr-t3@L72-L72 | direct use of bpN:p11:ext-class in the statement or proof at this span
EDGE: bpN:p11:s-real#data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:nr-t3@L72-L72 | direct use of bpN:p11:s-real#data in the statement or proof at this span
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:nr-t3@L72-L72 | direct use of bpN:p3:gen-sol in the statement or proof at this span
EDGE: bpN:p11:s-nf#data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:nr-t3@L72-L72 | direct use of bpN:p11:s-nf#data in the statement or proof at this span
EDGE: K:bp:p1:ext-integral | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:nr-t3@L72-L72 | direct package or input used by this proof step
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p7:exit-ball | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:nr-t3@L72-L72 | exit-ball lemma gives t* on the sphere of radius rho
EDGE: bpN:p11:real-system | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:nr-t3@L72-L72 | the bound ¦dot I-tilde¦<=eta/(e s-tilde) by Lemma real-system(c)
EDGE: stepN:p11:nr-nf | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:nr-t3@L72-L72 | eta<=e^{-kappa/6}eps, g and h theta-independent
EDGE: bpN:p11:ext-num | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:nr-t3@L72-L72 | e>2.718 so 6/(5e)<0.442
EDGE: bpN:p11:wfield | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:nr-t3@L72-L72 | the I-equation of X^c has no slow terms: dot I=-d_theta f_*
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-review-N-f
REVIEWER: sol-delta-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p11:nr-concl
KIND: step
TITLE: Transfer
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:nr-concl@L73-L73
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:nr-concl@L73-L73
CONTRACT_ID: stepN:p11:nr-concl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:nonresonant; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: u
SOURCE_CONCLUSION: ¦I(u)-I_c¦<=15r/32+2 r/2^7=31r/64<=r/2 by Lemma transfer
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:transfer, stepN:p11:nr-t12, stepN:p11:nr-t3
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:transfer | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:nr-concl@L73-L73 | Lemma transfer with (T1),(T2),(T3)
EDGE: stepN:p11:nr-t12 | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:nr-concl@L73-L73 | (T1),(T2)
EDGE: stepN:p11:nr-t3 | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:nr-concl@L73-L73 | (T3)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-review-N-f
REVIEWER: sol-delta-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpN:p11:energy-free
KIND: lemma
TITLE: Energy confinement near a resonance, convex case, no bound on $\omega$
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:energy-free@L78-L84
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:energy-free@L85-L109
CONTRACT_ID: bpN:p11:energy-free
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: r-tilde,s-tilde>0; I_c in R^n; Lambda subset Z^n, Pi=Pi_Lambda Euclidean projection; h holomorphic on V_{r-tilde}(I_c), real on real points, with m¦xi¦_2^2<=Q(I)[xi,xi], ¦Q(I)¦_{2->2}<=M on U={¦I-I_c¦<r-tilde} (0<m<=M); g,f_* in O(r-tilde,s-tilde)^{e,R} finite norms, P_Lambda g=g, zeta_g=¦g¦, eta=¦f_*¦, eps,eta-bar>0 with zeta_g<=(5/4)eps, eta<=eta-bar<=eps/e, eps<=m r-tilde^2/2^12, 16 k c s-tilde<=r-tilde; delta in (0,m r-tilde/16] with ¦Pi omega(I_c)¦_2<=delta, rho'=delta/(4M) (<=r-tilde/64), H-tilde=h+g+f_*, T_*=s-tilde m r-tilde/(20 M eta-bar)
SOURCE_QUANTIFIERS: r-tilde,s-tilde; I_c; Lambda; h; m,M; g,f_*; eps,eta-bar; delta; y-tilde
SOURCE_CONCLUSION: for every H-tilde-orbit y-tilde in W^e_{r-tilde} on J-tilde containing 0 with ¦I-tilde(0)-I_c¦_2<rho' and dist_inf(x-tilde(t),S-tilde)<r-tilde/2 for all t in J-tilde: ¦I-tilde(t)-I-tilde(0)¦_2<=r-tilde/4 for t in J-tilde, ¦t¦<=T_*
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p11:ef-tube, stepN:p11:ef-adm, stepN:p11:ef-en, stepN:p11:ef-id, stepN:p11:ef-C, stepN:p11:ef-contra, bpN:p7:exit-ball, bpN:p7:setting, bpN:p7:resonance-data, bpN:p11:ext-class, bpN:p11:s-real#data, bpN:p11:s-ext-class#data, bpN:p4:norm, bpN:p4:domains, bpN:p11:wfield, bpN:p3:gen-sol
EDGE: bpN:p4:norm | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:energy-free@L85-L109 | direct use of bpN:p4:norm in the statement or proof at this span
EDGE: bpN:p4:domains | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:energy-free@L85-L109 | direct use of bpN:p4:domains in the statement or proof at this span
EDGE: bpN:p11:wfield | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:energy-free@L85-L109 | direct use of bpN:p11:wfield in the statement or proof at this span
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:energy-free@L85-L109 | direct use of bpN:p3:gen-sol in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p11:ef-tube | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:energy-free@L87-L87 | proof step (orbit stretch lies in the small tube)
EDGE: stepN:p11:ef-adm | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:energy-free@L88-L88 | proof step (admissibility)
EDGE: stepN:p11:ef-en | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:energy-free@L89-L100 | proof step (energy inequality)
EDGE: stepN:p11:ef-id | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:energy-free@L101-L102 | proof step (the identity)
EDGE: stepN:p11:ef-C | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:energy-free@L103-L107 | proof step (estimate of C)
EDGE: stepN:p11:ef-contra | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:energy-free@L108-L108 | proof step (contradiction)
EDGE: bpN:p7:exit-ball | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:energy-free@L86-L86 | exit-ball lemma gives t* with ¦I-tilde(t*)-I-tilde(0)¦_2=r-tilde/4
EDGE: bpN:p7:setting | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:energy-free@L78-L79 | Q(I)=D^2 h_R(I), omega=d_I h, U, h_R
EDGE: bpN:p7:resonance-data | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:energy-free@L79-L79 | m-convexity of h on U and Pi_Lambda, Pi omega closeness
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:energy-free@L78-L80 | O^{e,R}, (SL)-type condition 16 k c s-tilde<=r-tilde
EDGE: bpN:p11:s-real#data | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:energy-free@L78-L84 | W^e_{r-tilde}, orbits
EDGE: bpN:p11:s-ext-class#data | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:energy-free@L79-L79 | weight c, S-tilde
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-review-N-f
REVIEWER: sol-delta-N-g
LEAN_STATUS: PROVED
LEAN_REF: energy_free (KAM/Nekhoroshev/Partial/Energy.lean)
LEAN_NOTE: audit N11-L2 PASS WITH NOTES; energy_free = exact signed statement (T_* with zeta as eta-bar); uses L1 energy_identity_re/transverse_pairing
NOTE: proved by contradiction from a violating time t_1 (preamble L86); new, unaudited mathematics per the blueprint. Dropped candidate edge bpN:p7:no-exit (\source: provenance; the lemma replaces it). Dependence of the time bound on omega is removed by the identity of step ef-id

NODE: stepN:p11:ef-tube
KIND: step
TITLE: The orbit stretch lies in the small tube
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-tube@L87-L87
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-tube@L87-L87
CONTRACT_ID: stepN:p11:ef-tube
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:energy-free; in the contradiction branch, t* and Delta are constructed by the first-exit argument; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: tau
SOURCE_CONCLUSION: ¦I-tilde(tau)-I_c¦<r-tilde/2 and y-tilde(tau) in D^e_{r-tilde/2,s-tilde/2} cap R^{2n+2k}; the segment [I-tilde(0),I-tilde(t*)] subset U
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:ext-class, bpN:p11:s-real#data, bpN:p4:domains, bpN:p11:s-ext-class#data, bpN:p3:gen-sol, bpN:p1:norm-compare
EDGE: bpN:p4:domains | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-tube@L87-L87 | direct use of bpN:p4:domains in the statement or proof at this span
EDGE: bpN:p11:s-ext-class#data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-tube@L87-L87 | direct use of bpN:p11:s-ext-class#data in the statement or proof at this span
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-tube@L87-L87 | direct use of bpN:p3:gen-sol in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-tube@L87-L87 | D^e_{r-tilde/2,s-tilde/2} (membership of the real points)
EDGE: bpN:p11:s-real#data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-tube@L87-L87 | W^e and the orbit y-tilde
EDGE: bpN:p1:norm-compare | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-tube@L87-L87 | the max action displacement is at most its Euclidean norm, giving membership in the smaller max-norm tube
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-delta-N-g
REVIEWER: sol-delta2-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p11:ef-adm
KIND: step
TITLE: Admissibility
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-adm@L88-L88
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-adm@L88-L88
CONTRACT_ID: stepN:p11:ef-adm
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:energy-free; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: I-tilde(0)
SOURCE_CONCLUSION: ¦omega_0-omega(I_c)¦_2<=M rho'=delta/4 so ¦Pi omega_0¦_2<=(5/4)delta; rho'<=m r-tilde/(64 M)<=r-tilde/64
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p1:ext-mvt, bpN:p7:setting, bpN:p7:resonance-data
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p1:ext-mvt | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-adm@L88-L88 | mean value inequality on the convex ball
EDGE: bpN:p7:setting | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-adm@L88-L88 | omega=d_I h and Q (Hessian bound M)
EDGE: bpN:p7:resonance-data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-adm@L88-L88 | Pi is the Euclidean orthogonal projection used in the bound for Pi omega_0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-delta-N-g
REVIEWER: sol-delta2-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p11:ef-en
KIND: step
TITLE: Energy inequality
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-en@L89-L89
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-en@L89-L100
CONTRACT_ID: stepN:p11:ef-en
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:energy-free; in the contradiction branch with the constructed first-exit time t*; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: t*
SOURCE_CONCLUSION: (m/2)Delta^2<=A+¦<Pi omega_0,Delta I>¦+C with A=¦(g+f_*)(y-tilde(t*))-(g+f_*)(y-tilde(0))¦<=2(zeta_g+eta), C=¦<omega_0,Pi^perp Delta I>¦, ¦<Pi omega_0,Delta I>¦<=(5/16)m Delta^2; hence (3/16)m Delta^2<=A+C and (3 m r-tilde^2)/256>0.0117 m r-tilde^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p11:ef-en-energy, stepN:p11:ef-en-taylor, stepN:p11:ef-en-split, bpN:p1:ext-restrict, bpN:p7:resonance-data, bpN:p4:norm, bpN:p11:ext-class, bpN:p11:s-real#data, bpN:p11:wfield, K:bp:p1:holomorphic-regularity
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p11:ef-en-energy | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-en@L91-L93 | substep: energy identity and bound A
EDGE: stepN:p11:ef-en-taylor | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-en@L95-L95 | substep: Lagrange Taylor along the fast segment
EDGE: stepN:p11:ef-en-split | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-en@L97-L100 | substep: projection split and the 5/16 bound
EDGE: bpN:p1:ext-restrict | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-en@L89-L89 | h_R=h¦_U is C^infty on U by restriction of scalars (holomorphic on V_r-tilde(I_c), real on real points)
EDGE: bpN:p7:resonance-data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-en@L89-L89 | U, m, Q=D^2 h_R, omega, the projection Pi and delta of the resonance data
EDGE: bpN:p4:norm | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-en@L89-L89 | extended-class norm of g and f_* (zeta_g, eta) in the data of the lemma
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-en@L89-L89 | extended phase space W^e_r-tilde and class O^e
EDGE: bpN:p11:s-real#data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-en@L89-L89 | extended real Hamiltonian H-tilde^R and orbit carrier
EDGE: bpN:p11:wfield | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-en@L89-L89 | X^c_{H-tilde^R}, the orbit of the extended field
EDGE: K:bp:p1:holomorphic-regularity | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-en@L89-L89 | the repeated local argument uses smoothness of holomorphic h on the arbitrary open action tube before restriction of scalars; fb-real(i),(ii) is the proof template, not an applicable centred-ball statement
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-delta-N-amend
REVIEWER: sol-delta2-N-amend
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Parent of ef-en-energy, ef-en-taylor, ef-en-split (G3). The inequality is proved directly in the extended phase space; Lemma bpN:p7:energy-core is NOT applied (it concerns canonical orbits of h_R(I)+g+f in R^n x R^n with g,f independent of the slow pair), so there is no edge to it, and only its argument is repeated along the fast action segment. The direct proof also uses projection algebra (self-adjointness, Pi+Pi^perp=1: bpN:p7:ext-linalg) and Euclidean Cauchy-Schwarz (bpN:p1:ext-norms); these uses are recorded at the substep ef-en-split, resolving the GLOBAL-delta FAIL.

NODE: stepN:p11:ef-en-energy
KIND: step
TITLE: Energy
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-en-energy@L91-L93
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-en-energy@L91-L93
CONTRACT_ID: stepN:p11:ef-en-energy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:energy-free; in the contradiction branch with the constructed first-exit time t*; Delta=¦Delta I¦_2=r-tilde/4, I_sigma=I-tilde(0)+sigma Delta I, omega_0=omega(I-tilde(0)), Q=D^2 h_R; y-tilde an H-tilde-orbit in W^e_r-tilde on an interval containing 0 and t*
SOURCE_QUANTIFIERS: t*
SOURCE_CONCLUSION: H-tilde^R∘y-tilde is constant, h_R(I-tilde(t*))-h_R(I-tilde(0))=-[(g+f_*)(y-tilde(t*))-(g+f_*)(y-tilde(0))], whose modulus is A<=2(zeta_g+eta) since ¦u(y)¦<=¦u¦_{r-tilde,s-tilde} at real y in W^e_r-tilde
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:real-system, bpN:p11:s-real#data, bpN:p11:ext-class, bpN:p11:wfield, bpN:p4:norm
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:real-system | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-en-energy@L91-L93 | (b) energy conservation along the orbit; (c) real-point bound ¦u(y)¦<=norm
EDGE: bpN:p11:s-real#data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-en-energy@L91-L91 | H-tilde^R=h_R(I)+(g+f_*)^R on W^e_r-tilde and the orbit carrier
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-en-energy@L93-L93 | g, f_* in the extended class on W^e_r-tilde
EDGE: bpN:p11:wfield | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-en-energy@L91-L91 | H-tilde-orbit of the weighted field X^c
EDGE: bpN:p4:norm | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-en-energy@L93-L93 | ¦u¦_{r-tilde,s-tilde} bounds g+f_* at real points
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-amend-N
REVIEWER: sol-delta-N-amend
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Substep of ef-en (G3): extended energy conservation, real-system (b),(c).

NODE: stepN:p11:ef-en-taylor
KIND: step
TITLE: Taylor along the fast segment
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-en-taylor@L95-L95
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-en-taylor@L95-L95
CONTRACT_ID: stepN:p11:ef-en-taylor
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:energy-free; in the contradiction branch with the constructed first-exit time t*; Delta=¦Delta I¦_2=r-tilde/4, I_sigma=I-tilde(0)+sigma Delta I, omega_0=omega(I-tilde(0)), Q=D^2 h_R; Q>=m on U; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: sigma in [0,1]
SOURCE_CONCLUSION: phi(sigma)=h_R(I_sigma) is C^2 with phi'(0)=<omega_0,Delta I>, phi''(sigma)=Q(I_sigma)[Delta I,Delta I]>=m Delta^2; Lagrange Taylor gives phi(1)-phi(0)-phi'(0)=(1/2)phi''(xi)>=(m/2)Delta^2, and with phi(1)-phi(0)<=A: (m/2)Delta^2<=A-<omega_0,Delta I>
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p11:ef-tube, stepN:p11:ef-en-energy, bpN:p7:ext-taylor, bpN:p1:ext-restrict, bpN:p7:resonance-data, K:bp:p1:holomorphic-regularity
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p11:ef-tube | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-en-taylor@L95-L95 | I_sigma in U for sigma in [0,1]
EDGE: stepN:p11:ef-en-energy | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-en-taylor@L95-L95 | the energy identity gives phi(1)-phi(0)<=A
EDGE: bpN:p7:ext-taylor | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-en-taylor@L95-L95 | Lagrange form of Taylor along the segment
EDGE: bpN:p1:ext-restrict | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-en-taylor@L95-L95 | phi is C^2 as h_R is C^infty on U
EDGE: bpN:p7:resonance-data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-en-taylor@L95-L95 | Q>=m on U (hypothesis on U)
EDGE: K:bp:p1:holomorphic-regularity | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-en-taylor@L95-L95 | holomorphic h on the open fast-action tube is C^infty; restriction of scalars then supplies the C^2 real function along I_sigma
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-amend-N+sol-delta-N-amend
REVIEWER: sol-delta2-N-amend
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Substep of ef-en (G3): one-variable Lagrange Taylor along the fast action segment.

NODE: stepN:p11:ef-en-split
KIND: step
TITLE: Splitting
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-en-split@L97-L100
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-en-split@L97-L100
CONTRACT_ID: stepN:p11:ef-en-split
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:energy-free; in the contradiction branch with the constructed first-exit time t*; Delta=¦Delta I¦_2=r-tilde/4, I_sigma=I-tilde(0)+sigma Delta I, omega_0=omega(I-tilde(0)), Q=D^2 h_R; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: Delta
SOURCE_CONCLUSION: <omega_0,Delta I>=<Pi omega_0,Delta I>+<omega_0,Pi^perp Delta I>, so (m/2)Delta^2<=A+¦<Pi omega_0,Delta I>¦+C, C=¦<omega_0,Pi^perp Delta I>¦; ¦<Pi omega_0,Delta I>¦<=(5/4)delta Delta<=(5/64)m r-tilde Delta=(5/16)m Delta^2 (r-tilde=4 Delta); hence (3/16)m Delta^2<=A+C and (3/16)m Delta^2=3 m r-tilde^2/256>0.0117 m r-tilde^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p11:ef-en-taylor, stepN:p11:ef-adm, bpN:p7:ext-linalg, bpN:p1:ext-norms, bpN:p7:resonance-data
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p11:ef-en-taylor | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-en-split@L97-L98 | the inequality (m/2)Delta^2<=A-<omega_0,Delta I> being split
EDGE: stepN:p11:ef-adm | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-en-split@L100-L100 | ¦Pi omega_0¦_2<=(5/4)delta
EDGE: bpN:p7:ext-linalg | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-en-split@L97-L97 | self-adjointness of Pi and Pi^perp=1-Pi split the linear term
EDGE: bpN:p1:ext-norms | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-en-split@L100-L100 | Euclidean Cauchy-Schwarz ¦<Pi omega_0,Delta I>¦<=¦Pi omega_0¦_2 Delta
EDGE: bpN:p7:resonance-data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-en-split@L97-L100 | Pi, delta, m of the resonance data (delta<=m r-tilde/16)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-amend-N+sol-delta-N-amend
REVIEWER: sol-delta2-N-amend
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Substep of ef-en (G3): projection algebra (ext-linalg) and Euclidean Cauchy-Schwarz (ext-norms); resolves the GLOBAL-delta FAIL on ef-en.

NODE: stepN:p11:ef-id
KIND: step
TITLE: The identity
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-id@L101-L102
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-id@L101-L102
CONTRACT_ID: stepN:p11:ef-id
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:energy-free; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: tau
SOURCE_CONCLUSION: F'=Df_*.X^c_{H-tilde^R}={f_*,H-tilde}_c={f_*,h}_c+{f_*,g}_c with {f_*,h}_c=d_theta f_*.omega(I-tilde), i.e. (eq:lie) d_theta f_*.omega(I-tilde(tau))=F'(tau)-{f_*,g}_c(y-tilde(tau))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:wfield, bpN:p11:ext-chain, bpN:p11:real-system, bpN:p11:s-ext-class#data, bpN:p11:s-real#data, bpN:p7:setting
EDGE: bpN:p11:s-ext-class#data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-id@L101-L102 | direct use of bpN:p11:s-ext-class#data in the statement or proof at this span
EDGE: bpN:p11:s-real#data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-id@L101-L102 | direct use of bpN:p11:s-real#data in the statement or proof at this span
EDGE: bpN:p7:setting | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-id@L101-L102 | direct package or input used by this proof step
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:wfield | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-id@L101-L102 | {u,v}_c=Du.X^c_v, antisymmetry
EDGE: bpN:p11:ext-chain | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-id@L101-L101 | chain rule along the curve
EDGE: bpN:p11:real-system | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-id@L101-L101 | X^c_{H-tilde^R} on W^e (Lemma real-system(a))
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-delta-N-g
REVIEWER: sol-delta2-N-g
LEAN_STATUS: PROVED
LEAN_REF: energy_identity, energy_identity_re (KAM/Nekhoroshev/Partial/EnergyIdentity.lean)
LEAN_NOTE: audit N11-L1-audit-1 ef-id PASS (ruling: L1 accepted)
NOTE: -

NODE: stepN:p11:ef-C
KIND: step
TITLE: Estimate of $C$
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-C@L103-L107
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-C@L103-L107
CONTRACT_ID: stepN:p11:ef-C
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:energy-free; in the same first-exit contradiction branch; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: t*
SOURCE_CONCLUSION: C<=¦F(t*)-F(0)¦+¦t*¦(sup¦{f_*,g}_c¦+M Delta sup¦d_theta f_*¦_2+(5/4)delta sup¦d_theta f_*¦_2) and, with ¦d_theta f_*¦_2<=eta/(e s-tilde) (real-system(c)) and ¦{f_*,g}_c¦<=4 eta zeta_g/(r-tilde s-tilde) (Lemma bracket with losses (r-tilde/2,s-tilde/2)), C<=2 eta-bar+0.0061 m r-tilde^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:real-system, stepN:p11:ef-id, bpN:p11:bracket, stepN:p11:ef-tube, stepN:p11:ef-adm, stepN:p11:ef-en, bpN:p11:ext-class, bpN:p11:ext-num, bpN:p4:norm, bpN:p4:domains, bpN:p11:wfield, K:bp:p1:ext-integral, K:bp:p1:ext-mvt, bpN:p7:setting, bpN:p7:resonance-data, bpN:p1:ext-norms
EDGE: bpN:p4:norm | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-C@L103-L107 | direct use of bpN:p4:norm in the statement or proof at this span
EDGE: bpN:p4:domains | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-C@L103-L107 | direct use of bpN:p4:domains in the statement or proof at this span
EDGE: bpN:p11:wfield | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-C@L103-L107 | direct use of bpN:p11:wfield in the statement or proof at this span
EDGE: K:bp:p1:ext-integral | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-C@L103-L107 | direct use of K:bp:p1:ext-integral in the statement or proof at this span
EDGE: K:bp:p1:ext-mvt | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-C@L103-L107 | direct use of K:bp:p1:ext-mvt in the statement or proof at this span
EDGE: bpN:p7:setting | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-C@L103-L107 | direct package or input used by this proof step
EDGE: bpN:p7:resonance-data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-C@L103-L107 | direct package or input used by this proof step
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:real-system | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-C@L103-L105 | Lemma real-system(c),(d): ¦d_theta f_*¦_2<=eta/(e s-tilde) and Pi^perp d_theta g=0
EDGE: stepN:p11:ef-id | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-C@L103-L104 | identity (eq:lie)
EDGE: bpN:p11:bracket | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-C@L105-L105 | Lemma bracket with (u,v)=(f_*,g), R_0=R=r-tilde, losses (r-tilde/2,s-tilde/2)
EDGE: stepN:p11:ef-tube | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-C@L105-L105 | the points y-tilde(tau) lie in D^e_{r-tilde/2,s-tilde/2}
EDGE: stepN:p11:ef-adm | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-C@L103-L105 | (5/4)delta bound for ¦Pi omega_0¦
EDGE: stepN:p11:ef-en | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-C@L103-L103 | definition of C
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-C@L105-L105 | (SL)_{rho,sigma} for the losses (r-tilde/2,s-tilde/2) is 16 k c s-tilde<=r-tilde
EDGE: bpN:p11:ext-num | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-C@L105-L106 | the listed 1/e<0.368 suffices for 5/4096+(5/64+1/4)/e<0.1220; the stronger printed decimal 0.3679 is not asserted by that external
EDGE: bpN:p1:ext-norms | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-C@L105-L105 | Euclidean norm of d_theta f_* is at most the sum of the component moduli bounded by real-system(c)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-delta-N-g
REVIEWER: sol-delta2-N-g
LEAN_STATUS: PROVED
LEAN_REF: energy_free (KAM/Nekhoroshev/Partial/Energy.lean); transverse_pairing (KAM/Nekhoroshev/Partial/EnergyIdentity.lean)
LEAN_NOTE: audit N11-L2 PASS WITH NOTES (row ef-C PASS) via ruling N11-L1-audit-1-ruling: ef-C is internal to energy_free (ef_theta_bound, ef_bracket_bound feeding L1 transverse_pairing); no standalone export
NOTE: -

NODE: stepN:p11:ef-contra
KIND: step
TITLE: Contradiction
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-contra@L108-L108
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-contra@L108-L108
CONTRACT_ID: stepN:p11:ef-contra
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:energy-free; in the same first-exit contradiction branch; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: t*
SOURCE_CONCLUSION: A+C<0.0071 m r-tilde^2<0.0117 m r-tilde^2, contradicting (3/16)m Delta^2>0.0117 m r-tilde^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p11:ef-en, stepN:p11:ef-C, bpN:p11:ext-num
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p11:ef-en | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-contra@L108-L108 | (3/16)m Delta^2<=A+C and the numerical lower bound
EDGE: stepN:p11:ef-C | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-contra@L108-L108 | C<=2 eta-bar+0.0061 m r-tilde^2
EDGE: bpN:p11:ext-num | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:ef-contra@L108-L108 | 1/e<0.368 for A<3.24 eps
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-review-N-f
REVIEWER: sol-delta-N-g
LEAN_STATUS: PROVED
LEAN_REF: energy_free (KAM/Nekhoroshev/Partial/Energy.lean)
LEAN_NOTE: audit N11-L2 PASS WITH NOTES; internal to energy_free (private ef_arith, ef_contra); exact rational contradiction with e>=2
NOTE: -

NODE: bpN:p11:resonant
KIND: proposition
TITLE: Resonant stability in the extended phase space, convex case
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:resonant@L111-L114
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:resonant@L115-L121
CONTRACT_ID: bpN:p11:resonant
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: r=r_B; s,K_a,alpha,delta>0; p=9/8, q=9, kappa=2 pi K_a s>=6; Lambda subset Z^n a subgroup; 0<m<=M; h holomorphic on V_r(I_c), real on real points, ¦d_I^2 h¦_{2->2}<=M on V_r(I_c), m-convex on U_r(I_c); ¦k.omega(I_c)¦>=alpha for k in Z_{K_a}\Lambda; cond-L with L=sqrt(n)M, K_a L r<=alpha/p; ¦Pi_Lambda omega(I_c)¦_2<=m r/32 (delta:=m r/32); (SL); f in O(r,s)^{e,R}, ¦f¦<=eps, eps>0, eps<=m r^2/2^14; H=h+f; T_Lambda=(s m r/(240 M eps))e^{kappa/6}
SOURCE_QUANTIFIERS: r,s,K_a,alpha,Lambda,m,M; h; f; eps; F; J; y; t_1
SOURCE_CONCLUSION: for every F with F=X^c_{H^R} on W^e_r, J containing 0, y with y'=F(y) on J, y(0)=(theta_0,I_c,x-tilde_0), x-tilde_0 in S-tilde, t_1 in J with ¦t_1¦<=T_Lambda and x-tilde(u) in S-tilde between 0 and t_1: ¦I(u)-I_c¦_2<=r/2 (so ¦I(u)-I_c¦<=r/2) between 0 and t_1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p11:rs-red, stepN:p11:rs-nf, stepN:p11:rs-t12, stepN:p11:rs-t3, stepN:p11:rs-concl, bpN:p6:setting, bpN:p7:resonance-data, bpN:p11:s-nf#data, bpN:p11:ext-class, bpN:p11:s-real#data, bpN:p11:s-ext-class#data, bpN:p4:norm, bpN:p4:domains, bpN:p11:wfield, bpN:p3:gen-sol, bpN:p6#data
EDGE: bpN:p4:norm | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:resonant@L115-L121 | direct use of bpN:p4:norm in the statement or proof at this span
EDGE: bpN:p4:domains | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:resonant@L115-L121 | direct use of bpN:p4:domains in the statement or proof at this span
EDGE: bpN:p11:wfield | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:resonant@L115-L121 | direct use of bpN:p11:wfield in the statement or proof at this span
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:resonant@L115-L121 | direct use of bpN:p3:gen-sol in the statement or proof at this span
EDGE: bpN:p6#data | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:resonant@L115-L121 | direct use of bpN:p6#data in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p11:rs-red | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:resonant@L116-L116 | proof step (reductions)
EDGE: stepN:p11:rs-nf | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:resonant@L117-L117 | proof step (normal form)
EDGE: stepN:p11:rs-t12 | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:resonant@L118-L118 | proof step ((T1),(T2))
EDGE: stepN:p11:rs-t3 | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:resonant@L119-L119 | proof step ((T3))
EDGE: stepN:p11:rs-concl | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:resonant@L120-L120 | proof step (conclusion)
EDGE: bpN:p6:setting | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:resonant@L112-L112 | cond-L, the nonresonance hypothesis modulo Lambda
EDGE: bpN:p7:resonance-data | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:resonant@L112-L113 | m-convexity and Pi_Lambda omega closeness to exact resonances
EDGE: bpN:p11:s-nf#data | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:resonant@L111-L113 | dictionary h on V_r(I_c), omega, K_a
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:resonant@L112-L112 | O^{e,R}, (SL)
EDGE: bpN:p11:s-real#data | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:resonant@L112-L112 | W^e_r, S-tilde, orbits
EDGE: bpN:p11:s-ext-class#data | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:resonant@L112-L112 | r=r_B, c, lambda
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-delta-N-g
REVIEWER: sol-delta2-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: dropped nothing material; the source (Pos93 Proposition 2) is provenance

NODE: stepN:p11:rs-red
KIND: step
TITLE: Reductions
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-red@L116-L116
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-red@L116-L116
CONTRACT_ID: stepN:p11:rs-red
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:resonant, in particular 0<eps<=m r^2/2^14; K_a L r<=alpha/p, L=sqrt(n)M, m<=M, q/p=8
SOURCE_QUANTIFIERS: eps
SOURCE_CONCLUSION: eps<=m r^2/2^14<=alpha r/(2^7 q K_a) (as alpha r/(2^7 q K_a)>=p sqrt(n)M r^2/(2^7 q)>=M r^2/2^10), so Theorem nf applies (Lambda=-Lambda)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:s-nf#data
EDGE: bpN:p11:s-nf#data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-red@L116-L116 | direct use of bpN:p11:s-nf#data in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-delta2-N-g
REVIEWER: sol-delta3-N-c
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p11:rs-nf
KIND: step
TITLE: Normal form
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-nf@L117-L117
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-nf@L117-L117
CONTRACT_ID: stepN:p11:rs-nf
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:resonant; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: f
SOURCE_CONCLUSION: Psi,g,f_* on D^e_{r/2,s/6}; ¦g¦<=¦g_0¦+16 c_1 eps^2<=(5/4)eps, eta<=eta-bar:=e^{-kappa/6}eps<=eps/e; r-tilde=r/2, s-tilde=s/6: eps<=m r-tilde^2/2^12, delta=m r-tilde/16, rho'=m r/(128 M), 16 k c s-tilde<r-tilde by (SL)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:nf, stepN:p11:rs-red, bpN:p11:ext-class, bpN:p4:norm, bpN:p4:domains, bpN:p11:s-nf#data, bpN:p4:projections, bpN:p11:ext-part4, bpN:p4:norm#monotone
EDGE: bpN:p4:norm | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-nf@L117-L117 | direct use of bpN:p4:norm in the statement or proof at this span
EDGE: bpN:p4:domains | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-nf@L117-L117 | direct use of bpN:p4:domains in the statement or proof at this span
EDGE: bpN:p11:s-nf#data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-nf@L117-L117 | direct use of bpN:p11:s-nf#data in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:nf | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-nf@L117-L117 | Theorem nf conclusions (a),(b)
EDGE: stepN:p11:rs-red | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-nf@L117-L117 | hypotheses of Theorem nf
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-nf@L117-L117 | (SL) gives 16 k c s-tilde<=r/12<r-tilde
EDGE: bpN:p4:projections | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-nf@L117-L117 | g_0=P_Lambda T_{K_a}f has weighted norm at most the perturbation norm eps
EDGE: bpN:p11:ext-part4 | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-nf@L117-L117 | the projection estimate is used for the extended Fourier class
EDGE: bpN:p4:norm#monotone | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-nf@L117-L117 | the g_0 projection bound is restricted from the initial domain to D^e_{r/2,s/6}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-delta-N-g
REVIEWER: sol-delta2-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p11:rs-t12
KIND: step
TITLE: (T1), (T2) in $\abs\cdot_*=\norm\cdot_2$
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-t12@L118-L118
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-t12@L118-L118
CONTRACT_ID: stepN:p11:rs-t12
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:resonant; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: x
SOURCE_CONCLUSION: (T1) with d_*=m r/(2^11 M)=rho'/16<rho' and d_x=r/2^10; (T2) as in Step nr-t12 via Lemma preimage
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:preimage, stepN:p11:nr-t12, bpN:p11:nf, stepN:p11:rs-nf, bpN:p11:s-nf#data, bpN:p1:norm-compare
EDGE: bpN:p11:s-nf#data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-t12@L118-L118 | direct use of bpN:p11:s-nf#data in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:preimage | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-t12@L118-L118 | (T2) via Lemma preimage
EDGE: stepN:p11:nr-t12 | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-t12@L118-L118 | as in Step nr-t12
EDGE: bpN:p11:nf | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-t12@L118-L118 | displacement bounds of Theorem nf(c)
EDGE: stepN:p11:rs-nf | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-t12@L118-L118 | r-tilde,s-tilde,rho'
EDGE: bpN:p1:norm-compare | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-t12@L118-L118 | Euclidean displacement is at most sqrt(n) times the max displacement in nf(c)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-delta-N-g
REVIEWER: sol-delta2-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p11:rs-t3
KIND: step
TITLE: (T3)
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-t3@L119-L119
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-t3@L119-L119
CONTRACT_ID: stepN:p11:rs-t3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:resonant; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: y-tilde
SOURCE_CONCLUSION: (T3): by Lemma energy-free (as d_*<rho') ¦I-tilde(t)-I-tilde(0)¦_2<=r-tilde/4 for ¦t¦<=T_Lambda; d_*+rho<r-tilde
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:energy-free, stepN:p11:rs-nf, stepN:p11:rs-t12, bpN:p11:ext-class, bpN:p11:s-ext-class#data, bpN:p11:s-real#data, bpN:p3:gen-sol, bpN:p11:s-nf#data
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-t3@L119-L119 | direct use of bpN:p11:ext-class in the statement or proof at this span
EDGE: bpN:p11:s-ext-class#data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-t3@L119-L119 | direct use of bpN:p11:s-ext-class#data in the statement or proof at this span
EDGE: bpN:p11:s-real#data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-t3@L119-L119 | direct use of bpN:p11:s-real#data in the statement or proof at this span
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-t3@L119-L119 | direct use of bpN:p3:gen-sol in the statement or proof at this span
EDGE: bpN:p11:s-nf#data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-t3@L119-L119 | direct use of bpN:p11:s-nf#data in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:energy-free | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-t3@L119-L119 | Lemma energy-free applies to such orbits
EDGE: stepN:p11:rs-nf | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-t3@L119-L119 | eta-bar, r-tilde, s-tilde, rho' and the identity T-tilde_*=T_Lambda
EDGE: stepN:p11:rs-t12 | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-t3@L119-L119 | d_*<rho' and d_x
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-review-N-f
REVIEWER: sol-delta-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p11:rs-concl
KIND: step
TITLE: Conclusion
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-concl@L120-L120
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-concl@L120-L120
CONTRACT_ID: stepN:p11:rs-concl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:resonant; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: u
SOURCE_CONCLUSION: ¦I(u)-I_c¦_2<=r-tilde/4+2 d_*<r/2 by Lemma transfer
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:transfer, stepN:p11:rs-t12, stepN:p11:rs-t3
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:transfer | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-concl@L120-L120 | Lemma transfer
EDGE: stepN:p11:rs-t12 | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-concl@L120-L120 | (T1),(T2)
EDGE: stepN:p11:rs-t3 | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:rs-concl@L120-L120 | (T3)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-review-N-f
REVIEWER: sol-delta-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpN:p11:hessian
KIND: lemma
TITLE: Hessian and sizes (nonempty $G$)
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:hessian@L125-L127
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:hessian@L128-L130
CONTRACT_ID: bpN:p11:hessian
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: h as in Theorem bpN:p0:partial (complex differentiable and complex C^2 on G'_rho, real on real points of G'_rho, ¦D^2 h(z)¦<=M_C on G'_rho, HasDefiniteFastPart G' rho g m h with sign sigma); G nonempty
SOURCE_QUANTIFIERS: n,k; G,G',D,rho,g,m,M_C,h; z in G'_rho; I in U
SOURCE_CONCLUSION: for z in G'_rho the symmetric matrix Q_C(z)=(D^2h(z)[e_i,e_j]) has ¦Q_C(z)¦_{2->2}<=M_C; for real I in U (real slice of G'_rho): Q(I)=D^2 h_R(I)=Q_C(I), m¦xi¦_2^2<=sigma Q(I)[xi,xi], ¦Q(I)[xi,xi]¦<=M_C¦xi¦_2^2, ¦omega(I)¦_inf>=g; consequently m<=M_C; for h_1=h/(2 pi) the same with (m_1,M_1,g_1)=(m,M_C,g)/(2 pi), and sigma h_1 is m_1-convex
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p11:hs-op, bpN:p0:partial-definite#HasDefiniteFastPart, bpN:p0:actionnbhd#actionNbhd, bpN:p11:constants, bpN:p11:hessian#real-hessian
EDGE: bpN:p11:hessian#real-hessian | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:hessian@L128-L130 | direct use of bpN:p11:hessian#real-hessian in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p11:hs-op | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:hessian@L129-L129 | proof step (operator norm)
EDGE: bpN:p0:partial-definite#HasDefiniteFastPart | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:hessian@L125-L126 | sigma and the definite fast part: ¦omega¦_inf>=g, m¦xi¦^2<=sigma Q[xi,xi]
EDGE: bpN:p0:actionnbhd#actionNbhd | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:hessian@L126-L126 | G'_rho and its real slice U
EDGE: bpN:p11:constants | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:hessian@L126-L126 | m_1,M_1,g_1
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-delta-N-g
REVIEWER: sol-delta2-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The real-Hessian identification is exposed by hessian#real-hessian; the Part 1 centred-ball lemma is a proof template, not a literal application on G-prime_rho. The Euclidean operator bound here is M_C, as stated, not n M_C.

NODE: stepN:p11:hs-op
KIND: step
TITLE: Operator norm
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:hs-op@L129-L129
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:hs-op@L129-L129
CONTRACT_ID: stepN:p11:hs-op
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:hessian (in particular the frozen max-norm bilinear operator bound on D(Dh), not an entrywise bound); prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: z; u,v
SOURCE_CONCLUSION: ¦D^2h(z)[u,v]¦<=M_C¦u¦_inf¦v¦_inf<=M_C¦u¦_2¦v¦_2, so ¦Q_C(z)¦_{2->2}<=M_C; real I in G' lies in G'_rho; m<=sigma Q[xi,xi]<=M_C at a real point of G for a unit vector gives m<=M_C
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p0:partial-definite#HasDefiniteFastPart, bpN:p0:actionnbhd#actionNbhd, bpN:p11:hessian#real-hessian, bpN:p1:norm-compare
EDGE: bpN:p11:hessian#real-hessian | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:hs-op@L129-L129 | direct use of bpN:p11:hessian#real-hessian in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p0:partial-definite#HasDefiniteFastPart | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:hs-op@L129-L129 | the definition of HasDefiniteFastPart (m¦xi¦^2<=sigma D^2 h_R[xi,xi], ¦omega¦_inf>=g)
EDGE: bpN:p0:actionnbhd#actionNbhd | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:hs-op@L129-L129 | G'_rho and I in bar B(I,rho) subset G'
EDGE: bpN:p1:norm-compare | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:hs-op@L129-L129 | max norms of the real or complex vectors are bounded by their Euclidean norms in the bilinear estimate
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-delta-N-g
REVIEWER: sol-delta2-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpN:p11:block-setting
KIND: definition
TITLE: Sets and the extended system for the block theorem
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:block-setting@L132-L134
PROOF_SOURCE: -
CONTRACT_ID: bpN:p11:block-setting
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data and constants of Definition bpN:p11:constants; G nonempty; mu>0 with eps=eps(mu)<=eps_0 and d=mu^{b_n}<=rho; I_c in G; a block starting radius r_B<=r_0
SOURCE_QUANTIFIERS: mu; I_c; r_B
SOURCE_CONCLUSION: defines S=core(D,3d/4) subset R^{2k}, w=d/4; the perturbation pair (h-breve,f-breve)=(sigma h_1,sigma f_1) with f_1(theta,I,x)=(mu/(2 pi))P((2 pi theta,q),(I,p)), x=(q,p); lambda=w/r_B, c=2 pi/lambda^2, W^e_varrho as in Section s-real, and the physical real set W(I_c,r_B)={(theta,I;x): ¦I-I_c¦<r_B, dist_inf(x,S)<w}
CONSTANT_SCOPE: constants as in Definition constants; I_c in G, r_B<=r_0
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:constants, bpN:p0:partial-core#innerCore, bpN:p0:partial-pert#IsPartialPerturbation, bpN:p11:s-ext-class#data, bpN:p11:s-real#data, bpN:p11:ext-class
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:block-setting@L132-L134 | direct use of bpN:p11:ext-class in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:constants | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:block-setting@L132-L133 | data and constants of Definition constants (eps_0, eps(mu), d, w, sigma, h_1)
EDGE: bpN:p0:partial-core#innerCore | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:block-setting@L133-L133 | S=core(D,3d/4)
EDGE: bpN:p0:partial-pert#IsPartialPerturbation | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:block-setting@L133-L133 | P of the perturbation pair is the IsPartialPerturbation function of the theorem
EDGE: bpN:p11:s-ext-class#data | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:block-setting@L133-L134 | lambda=w/r_B, c=2 pi/lambda^2, x-tilde and the block data
EDGE: bpN:p11:s-real#data | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:block-setting@L133-L133 | W^e_varrho as in Section s-real
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-delta-N-g
REVIEWER: sol-delta2-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: package bpN:p11:block-setting (SPEC)

NODE: bpN:p11:domain
KIND: lemma
TITLE: Analyticity, norm and field on the block domain
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:domain@L136-L138
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:domain@L139-L143
CONTRACT_ID: bpN:p11:domain
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Definition block-setting; I_c in G; 0<r_B<=r_0
SOURCE_QUANTIFIERS: I_c; r_B; mu
SOURCE_CONCLUSION: (a) h-breve holomorphic on V_{r_B}(I_c) subset G'_rho, real on real points, ¦d_I^2 h-breve¦_{2->2}<=M_1, m_1-convex on U_{r_B}(I_c), ¦omega¦_inf>=g_1; (b) f-breve in O(r_B,s)^{e,R}, ¦f-breve¦_{r_B,s}<=eps(mu)=kappa_C mu/(2 pi); (c) on the open set W(I_c,r_B) the frozen H-hat_mu=(1/(2 pi))H_mu o Theta^{-1} equals Re(h_1+f_1) and is real analytic, so sigma X^{2pi}_{H-hat_mu}=X^{2pi}_{(h-breve+f-breve)^R} there; in x-tilde=x/lambda this is X^c_{(h-breve+f-breve)^R} on W^e_{r_B}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p11:dm-pts, stepN:p11:dm-norm, stepN:p11:dm-field, bpN:p11:block-setting, bpN:p11:ext-class, bpN:p11:s-real#data, bpN:p11:orbit, bpN:p4:norm, bpN:p4:domains, bpN:p11:wfield, bpN:p11:s-ext-class#data, bpN:p11:constants
EDGE: bpN:p4:norm | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:domain@L139-L143 | direct use of bpN:p4:norm in the statement or proof at this span
EDGE: bpN:p4:domains | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:domain@L139-L143 | direct use of bpN:p4:domains in the statement or proof at this span
EDGE: bpN:p11:wfield | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:domain@L139-L143 | direct use of bpN:p11:wfield in the statement or proof at this span
EDGE: bpN:p11:s-ext-class#data | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:domain@L139-L143 | direct use of bpN:p11:s-ext-class#data in the statement or proof at this span
EDGE: bpN:p11:constants | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:domain@L139-L143 | direct use of bpN:p11:constants in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p11:dm-pts | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:domain@L140-L140 | proof step (complex points)
EDGE: stepN:p11:dm-norm | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:domain@L141-L141 | proof step (norm)
EDGE: stepN:p11:dm-field | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:domain@L142-L142 | proof step (field)
EDGE: bpN:p11:block-setting | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:domain@L137-L137 | Definition block-setting
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:domain@L137-L137 | O^{e,R}, W^e
EDGE: bpN:p11:s-real#data | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:domain@L137-L137 | W^e_{r_B}
EDGE: bpN:p11:orbit | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:domain@L137-L137 | H-hat_mu=(1/(2 pi))H_mu o Theta^{-1}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-delta-N-g
REVIEWER: sol-delta2-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p11:dm-pts
KIND: step
TITLE: Complex points
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:dm-pts@L140-L140
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:dm-pts@L140-L140
CONTRACT_ID: stepN:p11:dm-pts
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: complex (theta,I,x) with ¦Im theta¦<2s=rho/(2 pi), ¦I-I_c¦<r_B<=rho/2, dist_inf(x,S)<w
SOURCE_QUANTIFIERS: z
SOURCE_CONCLUSION: z=((2 pi theta,q),(I,p)) lies in F(G',D,rho); so f_1 is holomorphic (P1), ¦f_1¦<=mu/(2 pi) (P2), 1-periodic in theta (P4), real at real points (P3), and V_{r_B}(I_c) subset G'_rho; (a) follows from Lemma hessian
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p0:partial-domain#partialComplexDomain, bpN:p0:partial-pert#IsPartialPerturbation, bpN:p0:partial-core#innerCore, bpN:p0:actionnbhd#actionNbhd, bpN:p0:strip#complexStrip, bpN:p11:hessian, bpN:p11:constants, bpN:p11:block-setting, bpN:p4:domains
EDGE: bpN:p4:domains | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:dm-pts@L140-L140 | direct use of bpN:p4:domains in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p0:partial-domain#partialComplexDomain | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:dm-pts@L140-L140 | membership in F(G',D,rho)
EDGE: bpN:p0:partial-pert#IsPartialPerturbation | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:dm-pts@L140-L140 | (P1)-(P4) of P on F(G',D,rho)
EDGE: bpN:p0:partial-core#innerCore | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:dm-pts@L140-L140 | x_0 in S=core(D,3d/4) gives bar B(x_0,d/4) subset D
EDGE: bpN:p0:actionnbhd#actionNbhd | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:dm-pts@L140-L140 | Re I within rho/2 of I_c lies in G' (collar), V subset G'_rho
EDGE: bpN:p0:strip#complexStrip | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:dm-pts@L140-L140 | ¦Im 2 pi theta_i¦<rho, ¦Im I_i¦<rho/2: membership in the complex strips
EDGE: bpN:p11:hessian | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:dm-pts@L140-L140 | (a) follows from Lemma hessian
EDGE: bpN:p11:constants | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:dm-pts@L140-L140 | s=rho/(4 pi), r_0<=rho/2, w=d/4
EDGE: bpN:p11:block-setting | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:dm-pts@L140-L140 | S, w, f_1 of block-setting
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-review-N-f
REVIEWER: sol-delta-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p11:dm-norm
KIND: step
TITLE: Norm
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:dm-norm@L141-L141
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:dm-norm@L141-L141
CONTRACT_ID: stepN:p11:dm-norm
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:domain; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: f_1
SOURCE_CONCLUSION: ¦f_1¦_{r_B,s}<=coth(pi s)^n mu/(2 pi) (the bound holds on D^e_{r_B,2s})
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:ext-part4, bpN:p4:sup-weighted, stepN:p11:dm-pts, bpN:p11:constants, bpN:p4:norm, bpN:p4:domains, bpN:p11:ext-class
EDGE: bpN:p4:norm | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:dm-norm@L141-L141 | direct use of bpN:p4:norm in the statement or proof at this span
EDGE: bpN:p4:domains | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:dm-norm@L141-L141 | direct use of bpN:p4:domains in the statement or proof at this span
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:dm-norm@L141-L141 | direct use of bpN:p11:ext-class in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:ext-part4 | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:dm-norm@L141-L141 | B.1(b) for the extended class
EDGE: bpN:p4:sup-weighted | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:dm-norm@L141-L141 | B.1(b) with sigma=s
EDGE: stepN:p11:dm-pts | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:dm-norm@L141-L141 | holomorphy, periodicity and ¦f_1¦<=mu/(2 pi) on D^e_{r_B,2s}
EDGE: bpN:p11:constants | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:dm-norm@L141-L141 | kappa_C=coth(pi s)^n, eps(mu)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-review-N-f
REVIEWER: sol-delta-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p11:dm-field
KIND: step
TITLE: Field
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:dm-field@L142-L142
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:dm-field@L142-L142
CONTRACT_ID: stepN:p11:dm-field
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:domain; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: y
SOURCE_CONCLUSION: H-hat_mu is the real part of a holomorphic function, so Lemma real-system(a) applies; rescaling x=lambda x-tilde turns weight 2 pi into c; sigma X^{2pi}_{H-hat_mu}=X^{2pi}_{(h-breve+f-breve)^R} on W(I_c,r_B)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:real-system, bpN:p11:ext-class, bpN:p11:orbit, bpN:p0:partial-sec#degenerateHamiltonian, bpN:p0:partial-complexify#complexifyPhase, bpN:p0:realpart#realPart, stepN:p11:dm-pts, bpN:p11:wfield, bpN:p11:s-ext-class#data, bpN:p11:constants, bpN:p11:block-setting
EDGE: bpN:p11:s-ext-class#data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:dm-field@L142-L142 | direct use of bpN:p11:s-ext-class#data in the statement or proof at this span
EDGE: bpN:p11:constants | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:dm-field@L142-L142 | direct use of bpN:p11:constants in the statement or proof at this span
EDGE: bpN:p11:block-setting | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:dm-field@L142-L142 | direct use of bpN:p11:block-setting in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:real-system | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:dm-field@L142-L142 | Lemma real-system(a)
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:dm-field@L142-L142 | rescaling x=lambda x-tilde, weight c (Definition ext-class)
EDGE: bpN:p11:orbit | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:dm-field@L142-L142 | H-hat_mu and its field X^{2pi}
EDGE: bpN:p0:partial-sec#degenerateHamiltonian | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:dm-field@L142-L142 | H_mu=Re h+mu Re(P o cx) on real points
EDGE: bpN:p0:partial-complexify#complexifyPhase | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:dm-field@L142-L142 | cx z in F
EDGE: bpN:p0:realpart#realPart | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:dm-field@L142-L142 | Re h
EDGE: stepN:p11:dm-pts | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:dm-field@L142-L142 | holomorphy of f_1, periodicity, and the points in F
EDGE: bpN:p11:wfield | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:dm-field@L142-L142 | X^{2pi}, X^c
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-review-N-f
REVIEWER: sol-delta-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpN:p11:block-data
KIND: lemma
TITLE: Block data from the covering lemma
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:block-data@L145-L148
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:block-data@L149-L153
CONTRACT_ID: bpN:p11:block-data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Definition block-setting; kappa=2 pi K_a s>=6 (K_a=K/sqrt n, K=(eps_0/eps)^{1/(2n)}>=1); I_0 in G; p=9/8, q=9, b_c=1/32; Lemma covering applied with (P,omega)=({I_0},omega_{h_1}) and parameters (p,b_c,r_0,M_1,m_1,K,A) (A=40M_1/m_1>=36 M_1/m_1+sqrt 2)
SOURCE_QUANTIFIERS: I_0; mu; K,K_a
SOURCE_CONCLUSION: there is Lambda in M_K with I_0 in D_Lambda, Lambda not Z^n, and with r=r_Lambda, alpha=alpha_Lambda=p M_1 K r: (1) r_Theta=r_0/(AK)^n<=r<=R_0/K; (2) ¦k.omega(I_0)¦>=alpha for k in Z_{K_a}\Lambda (Lambda=Theta: 0<¦k¦_1<=K_a with alpha_Theta); (3) ¦Pi_Lambda omega(I_0)¦_2<m_1 r/32; (4) cond-L holds on V_r(I_0) with L=sqrt(n)M_1 and K_a L r=alpha/p; (5) eps<=m_1 r^2/2^14 and eps<=alpha r/(2^7 q K_a)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p11:bd-cover, stepN:p11:bd-24, stepN:p11:bd-5, bpN:p11:block-setting, bpN:p8:covering, bpN:p8:klattice, bpN:p8:blocks, bpN:p6:setting, bpN:p11:constants, bpN:p4:domains, bpN:p7:resonance-data, bpN:p6#data
EDGE: bpN:p4:domains | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:block-data@L149-L153 | direct use of bpN:p4:domains in the statement or proof at this span
EDGE: bpN:p7:resonance-data | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:block-data@L149-L153 | direct use of bpN:p7:resonance-data in the statement or proof at this span
EDGE: bpN:p6#data | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:block-data@L149-L153 | direct use of bpN:p6#data in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p11:bd-cover | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:block-data@L150-L150 | proof step (covering)
EDGE: stepN:p11:bd-24 | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:block-data@L151-L151 | proof step ((2)-(4))
EDGE: stepN:p11:bd-5 | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:block-data@L152-L152 | proof step ((5))
EDGE: bpN:p11:block-setting | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:block-data@L145-L146 | Definition block-setting
EDGE: bpN:p8:covering | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:block-data@L146-L146 | Lemma covering applied
EDGE: bpN:p8:klattice | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:block-data@L146-L146 | M_K, the maximal K-lattices
EDGE: bpN:p8:blocks | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:block-data@L147-L147 | D_Lambda, r_Lambda, alpha_Lambda, delta_Lambda, Theta
EDGE: bpN:p6:setting | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:block-data@L147-L147 | cond-L
EDGE: bpN:p11:constants | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:block-data@L145-L146 | K, K_a, kappa, eps_0, A, R_0, r_0, b_c
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-delta-N-g
REVIEWER: sol-delta2-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: dropped candidate edge bpN:p11:hom (appears only as the check that omega is real, "as required by Proposition hom"; hom is not used here)

NODE: stepN:p11:bd-cover
KIND: step
TITLE: Covering
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bd-cover@L150-L150
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bd-cover@L150-L150
CONTRACT_ID: stepN:p11:bd-cover
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:block-data; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: I_0
SOURCE_CONCLUSION: Lambda in M_K with I_0 in D_Lambda and r_Theta<=r_Lambda<=r_0/(AK)=R_0/K for Lambda not Z^n; Lambda=Z^n is impossible since ¦omega(I_0)¦_2<delta_{Z^n}=m_1 r_0/32<=g_1<=¦omega(I_0)¦_inf
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p8:covering, bpN:p11:hessian, bpN:p11:constants, bpN:p11:block-setting, bpN:p7:resonance-data, bpN:p8:klattice, bpN:p8:blocks, bpN:p1:norm-compare
EDGE: bpN:p7:resonance-data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bd-cover@L150-L150 | direct use of bpN:p7:resonance-data in the statement or proof at this span
EDGE: bpN:p8:klattice | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bd-cover@L150-L150 | direct use of bpN:p8:klattice in the statement or proof at this span
EDGE: bpN:p8:blocks | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bd-cover@L150-L150 | direct package or input used by this proof step
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p8:covering | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bd-cover@L150-L150 | Lemma covering(a),(d), and (c) for the case Lambda=Z^n
EDGE: bpN:p11:hessian | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bd-cover@L150-L150 | ¦omega(I_0)¦_inf>=g_1 (Lemma hessian)
EDGE: bpN:p11:constants | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bd-cover@L150-L150 | r_0<=32 g/m so m_1 r_0/32<=g_1; R_0=r_0/A
EDGE: bpN:p11:block-setting | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bd-cover@L150-L150 | omega_{h_1}
EDGE: bpN:p1:norm-compare | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bd-cover@L150-L150 | the Euclidean frequency norm is at least its max norm in the full-rank exclusion
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-delta-N-g
REVIEWER: sol-delta2-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p11:bd-24
KIND: step
TITLE: (2)--(4)
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bd-24@L151-L151
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bd-24@L151-L151
CONTRACT_ID: stepN:p11:bd-24
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:block-data; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: I_0
SOURCE_CONCLUSION: (2),(3) from Corollary cutoffs(b),(c) (delta_Lambda=b_c m_1 r); (4) cond-L with L=sqrt(n)M_1 from the Euclidean Hessian bound (¦d_I^2 h_1 v¦_inf<=M_1¦v¦_2<=sqrt(n)M_1¦v¦_inf) and K_a L r=alpha/p; sign transport omega_{sigma h_1}=sigma omega_{h_1}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p8:cutoffs, bpN:p6:lipschitz, bpN:p11:domain, stepN:p11:bd-cover, bpN:p11:hessian, bpN:p11:constants, bpN:p7:resonance-data, bpN:p6:setting, bpN:p1:norm-compare
EDGE: bpN:p11:constants | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bd-24@L151-L151 | direct use of bpN:p11:constants in the statement or proof at this span
EDGE: bpN:p7:resonance-data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bd-24@L151-L151 | direct use of bpN:p7:resonance-data in the statement or proof at this span
EDGE: bpN:p6:setting | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bd-24@L151-L151 | direct package or input used by this proof step
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p8:cutoffs | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bd-24@L151-L151 | Corollary cutoffs(b),(c) with K_g=K, K_a=K/sqrt n
EDGE: bpN:p6:lipschitz | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bd-24@L151-L151 | operator-norm Hessian bound gives cond-L (Lemma lipschitz-type)
EDGE: bpN:p11:domain | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bd-24@L151-L151 | omega_{sigma h_1} real on the real slice; ¦d_I^2 h-breve¦_{2->2}<=M_1
EDGE: stepN:p11:bd-cover | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bd-24@L151-L151 | Lambda, r=r_Lambda, alpha=alpha_Lambda
EDGE: bpN:p11:hessian | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bd-24@L151-L151 | Euclidean Hessian bound M_1 for h_1
EDGE: bpN:p1:norm-compare | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bd-24@L151-L151 | max<=Euclidean<=sqrt(n) max converts the Euclidean Hessian bound to the max-norm frequency Lipschitz constant
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-delta-N-g
REVIEWER: sol-delta2-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p11:bd-5
KIND: step
TITLE: (5)
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bd-5@L152-L152
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bd-5@L152-L152
CONTRACT_ID: stepN:p11:bd-5
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:block-data; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: I_0
SOURCE_CONCLUSION: m_1 r_Theta^2/2^14=eps_0 K^{-2n}=eps and r>=r_Theta; alpha r/(2^7 q K_a)=p sqrt(n)M_1 r^2/(2^7 q)>=M_1 r^2/2^10>=m_1 r^2/2^14>=eps
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:constants, stepN:p11:bd-cover, bpN:p11:hessian
EDGE: bpN:p11:hessian | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bd-5@L152-L152 | direct package or input used by this proof step
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:constants | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bd-5@L152-L152 | eps_0, eps(mu), K=(eps_0/eps)^{1/(2n)}, r_Theta
EDGE: stepN:p11:bd-cover | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bd-5@L152-L152 | r>=r_Theta
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-review-N-f
REVIEWER: sol-delta-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpN:p11:block
KIND: theorem
TITLE: Stopped block stability (Pos93 Theorem 1 with slow parameters)
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:block@L155-L158
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:block@L159-L166
CONTRACT_ID: bpN:p11:block
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Definition block-setting; (B1) kappa=2 pi K_a s>=6; (B2) K>=256 k rho R_0/d^2; r_Theta=r_0/(AK)^n, T_P=s m_1 r_Theta e^{kappa/6}/(240 M_1 eps); I_0 in G; F: R^{2n+2k}->R^{2n+2k} any function with F=X^{2pi}_{(h-breve+f-breve)^R} on W(I_0,r_0); J containing 0 an interval; y=(theta,I;x) differentiable on J with y'=F(y) there, I(0)=I_0, x(0) in S; t_1 in J with ¦t_1¦<=T_P and x(u) in core(D,d) for all u between 0 and t_1
SOURCE_QUANTIFIERS: I_0; F; J; y; t_1
SOURCE_CONCLUSION: ¦I(u)-I_0¦_inf<=R_0/(2K) for all u between 0 and t_1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p11:bl-block, stepN:p11:bl-sl, stepN:p11:bl-ext, stepN:p11:bl-theta, stepN:p11:bl-res, bpN:p11:block-setting, bpN:p11:constants, bpN:p0:partial-core#innerCore, bpN:p4:norm, bpN:p4:domains, bpN:p11:ext-class, bpN:p11:wfield, bpN:p11:s-ext-class#data, bpN:p11:s-real#data, bpN:p1:norm-compare
EDGE: bpN:p4:norm | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:block@L159-L166 | direct use of bpN:p4:norm in the statement or proof at this span
EDGE: bpN:p4:domains | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:block@L159-L166 | direct use of bpN:p4:domains in the statement or proof at this span
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:block@L159-L166 | direct use of bpN:p11:ext-class in the statement or proof at this span
EDGE: bpN:p11:wfield | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:block@L159-L166 | direct use of bpN:p11:wfield in the statement or proof at this span
EDGE: bpN:p11:s-ext-class#data | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:block@L159-L166 | direct use of bpN:p11:s-ext-class#data in the statement or proof at this span
EDGE: bpN:p11:s-real#data | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:block@L159-L166 | direct use of bpN:p11:s-real#data in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p11:bl-block | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:block@L161-L161 | proof step (block)
EDGE: stepN:p11:bl-sl | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:block@L162-L162 | proof step ((SL))
EDGE: stepN:p11:bl-ext | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:block@L163-L163 | proof step (extended system)
EDGE: stepN:p11:bl-theta | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:block@L164-L164 | proof step (case Lambda=Theta)
EDGE: stepN:p11:bl-res | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:block@L165-L165 | proof step (case Lambda not Theta, Z^n)
EDGE: bpN:p11:block-setting | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:block@L155-L156 | Definition block-setting
EDGE: bpN:p11:constants | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:block@L156-L157 | K, K_a, kappa, A, R_0, r_0, eps, d, s, m_1, M_1
EDGE: bpN:p0:partial-core#innerCore | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:block@L156-L156 | x(u) in core(D,d)
EDGE: bpN:p1:norm-compare | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:block@L165-L165 | the resonant branch gives a Euclidean action bound, which implies the max-norm conclusion of the block theorem
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-delta-N-g
REVIEWER: sol-delta2-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: dropped candidate edge bpN:p11:b-change (explanatory remark: the covering parameter b_c=1/32 is fixed in Definition constants and used in Lemma block-data)

NODE: stepN:p11:bl-block
KIND: step
TITLE: Block
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-block@L161-L161
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-block@L161-L161
CONTRACT_ID: stepN:p11:bl-block
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:block; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: I_0
SOURCE_CONCLUSION: Lambda, r=r_Lambda in [r_Theta,R_0/K], alpha; take r_B=r, lambda=w/r, c=2 pi r^2/w^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:block-data, bpN:p11:s-ext-class#data, bpN:p11:constants, bpN:p11:block-setting, bpN:p8:klattice, bpN:p8:blocks
EDGE: bpN:p11:constants | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-block@L161-L161 | direct use of bpN:p11:constants in the statement or proof at this span
EDGE: bpN:p11:block-setting | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-block@L161-L161 | direct use of bpN:p11:block-setting in the statement or proof at this span
EDGE: bpN:p8:klattice | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-block@L161-L161 | direct package or input used by this proof step
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:block-data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-block@L161-L161 | Lemma block-data gives Lambda, r_Lambda, alpha
EDGE: bpN:p11:s-ext-class#data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-block@L161-L161 | lambda=w/r_B, c=2 pi r_B^2/w^2
EDGE: bpN:p8:blocks | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-block@L161-L161 | the chosen lattice radius r_Lambda and alpha are block data used directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-delta-N-g
REVIEWER: sol-delta2-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p11:bl-sl
KIND: step
TITLE: (SL)
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-sl@L162-L162
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-sl@L162-L162
CONTRACT_ID: stepN:p11:bl-sl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:block; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: r
SOURCE_CONCLUSION: 64 pi k s r<=64 pi k s R_0/K=16 k rho R_0/K<=d^2/16=w^2, i.e. (SL) (this is the only place where d, hence b_n, enters)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p11:bl-block, bpN:p11:constants, bpN:p11:ext-class
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p11:bl-block | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-sl@L162-L162 | r=r_Lambda<=R_0/K
EDGE: bpN:p11:constants | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-sl@L162-L162 | s=rho/(4 pi), w=d/4
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-sl@L162-L162 | (SL) as 64 pi k s r_B<=w^2
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-review-N-f
REVIEWER: sol-delta-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p11:bl-ext
KIND: step
TITLE: Extended system
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-ext@L163-L163
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-ext@L163-L163
CONTRACT_ID: stepN:p11:bl-ext
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:block; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: y-tilde
SOURCE_CONCLUSION: h-breve on V_r(I_0), f-breve in O(r,s)^{e,R} with ¦f-breve¦<=eps; y-tilde=(theta,I,x/lambda) satisfies y-tilde'=F~(y-tilde) with F~=X^c_{(h+f)^R} on W^e_r subset image of W(I_0,r_0); x-tilde(u) in S-tilde since core(D,d) subset S
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:domain, bpN:p11:ext-class, bpN:p11:s-real#data, stepN:p11:bl-block, bpN:p0:partial-core#innerCore, bpN:p4:norm, bpN:p4:domains, bpN:p11:wfield, bpN:p11:s-ext-class#data, bpN:p11:constants, bpN:p11:block-setting
EDGE: bpN:p4:norm | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-ext@L163-L163 | direct use of bpN:p4:norm in the statement or proof at this span
EDGE: bpN:p4:domains | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-ext@L163-L163 | direct use of bpN:p4:domains in the statement or proof at this span
EDGE: bpN:p11:wfield | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-ext@L163-L163 | direct use of bpN:p11:wfield in the statement or proof at this span
EDGE: bpN:p11:s-ext-class#data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-ext@L163-L163 | direct use of bpN:p11:s-ext-class#data in the statement or proof at this span
EDGE: bpN:p11:constants | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-ext@L163-L163 | direct use of bpN:p11:constants in the statement or proof at this span
EDGE: bpN:p11:block-setting | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-ext@L163-L163 | direct use of bpN:p11:block-setting in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:domain | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-ext@L163-L163 | Lemma domain (a),(b),(c)
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-ext@L163-L163 | O^{e,R}, W^e_r, S-tilde
EDGE: bpN:p11:s-real#data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-ext@L163-L163 | W^e_r and orbits
EDGE: stepN:p11:bl-block | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-ext@L163-L163 | r_B=r, lambda, c
EDGE: bpN:p0:partial-core#innerCore | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-ext@L163-L163 | core(D,d) subset S=core(D,3d/4)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-review-N-f
REVIEWER: sol-delta-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p11:bl-theta
KIND: step
TITLE: Case $\Lambda=\Theta$
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-theta@L164-L164
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-theta@L164-L164
CONTRACT_ID: stepN:p11:bl-theta
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:block; branch Lambda=Theta; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: y
SOURCE_CONCLUSION: Proposition nonresonant with (r_Theta-block: r,K_a,alpha_Theta,sqrt(n)M_1), p=9/8: hypotheses by block-data (2),(4),(5), (B1), (SL); T_nr=s r e^{kappa/6}/(5 eps)>=T_P (r=r_Theta for Theta; m_1/M_1<=1); conclusion ¦I(u)-I_0¦<=r/2<=R_0/(2K)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:nonresonant, bpN:p11:block-data, stepN:p11:bl-block, stepN:p11:bl-sl, stepN:p11:bl-ext, bpN:p11:hessian, bpN:p11:ext-class, bpN:p11:constants, bpN:p11:block-setting
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-theta@L164-L164 | direct use of bpN:p11:ext-class in the statement or proof at this span
EDGE: bpN:p11:constants | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-theta@L164-L164 | direct use of bpN:p11:constants in the statement or proof at this span
EDGE: bpN:p11:block-setting | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-theta@L164-L164 | direct package or input used by this proof step
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:nonresonant | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-theta@L164-L164 | Proposition nonresonant
EDGE: bpN:p11:block-data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-theta@L164-L164 | block-data (2),(4),(5)
EDGE: stepN:p11:bl-block | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-theta@L164-L164 | r, alpha, K_a
EDGE: stepN:p11:bl-sl | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-theta@L164-L164 | (SL)
EDGE: stepN:p11:bl-ext | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-theta@L164-L164 | h-breve, f-breve and the extended system
EDGE: bpN:p11:hessian | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-theta@L164-L164 | m_1/M_1<=1 (m<=M_C)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-review-N-f
REVIEWER: sol-delta-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p11:bl-res
KIND: step
TITLE: Case $\Lambda\ne\Theta,\Z^n$
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-res@L165-L165
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-res@L165-L165
CONTRACT_ID: stepN:p11:bl-res
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p11:block; branch Lambda distinct from Theta and Z^n; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: y
SOURCE_CONCLUSION: Proposition resonant with (r,K_a,alpha,m,M)=(r_Lambda,K_a,alpha_Lambda,m_1,M_1): hypotheses by block-data (2)-(5), (B1), (SL), m_1-convexity (Lemma domain(a)); T_Lambda=s m_1 r_Lambda e^{kappa/6}/(240 M_1 eps)>=T_P since r_Lambda>=r_Theta; conclusion ¦I(u)-I_0¦_2<=r_Lambda/2<=R_0/(2K)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:resonant, bpN:p11:block-data, stepN:p11:bl-block, stepN:p11:bl-sl, stepN:p11:bl-ext, bpN:p11:domain, bpN:p11:ext-class, bpN:p11:constants, bpN:p11:block-setting
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-res@L165-L165 | direct use of bpN:p11:ext-class in the statement or proof at this span
EDGE: bpN:p11:constants | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-res@L165-L165 | direct use of bpN:p11:constants in the statement or proof at this span
EDGE: bpN:p11:block-setting | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-res@L165-L165 | direct package or input used by this proof step
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:resonant | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-res@L165-L165 | Proposition resonant
EDGE: bpN:p11:block-data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-res@L165-L165 | block-data (1)-(5)
EDGE: stepN:p11:bl-block | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-res@L165-L165 | r_Lambda, alpha_Lambda
EDGE: stepN:p11:bl-sl | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-res@L165-L165 | (SL)
EDGE: stepN:p11:bl-ext | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-res@L165-L165 | h-breve, f-breve and the extended system
EDGE: bpN:p11:domain | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:bl-res@L165-L165 | m_1-convexity (Lemma domain(a))
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-review-N-f
REVIEWER: sol-delta-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p11:final-empty
KIND: step
TITLE: Empty $G$
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-empty@L171-L171
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-empty@L171-L171
CONTRACT_ID: stepN:p11:final-empty
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: G=empty or nonempty
SOURCE_QUANTIFIERS: G
SOURCE_CONCLUSION: if G=empty then core(G,.)=empty and (Z2) is impossible, any mu_0>0 works; otherwise G nonempty and Lemma hessian (m<=M_C) holds
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p0:partial-core#innerCore, bpN:p11:hessian
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p0:partial-core#innerCore | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-empty@L171-L171 | core(G,mu^{b_n})=empty when G=empty
EDGE: bpN:p11:hessian | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-empty@L171-L171 | Lemma hessian (m<=M_C) for G nonempty
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c
REVIEWER: sol-review-N-f
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p11:final-data
KIND: step
TITLE: Data and constants
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-data@L172-L172
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-data@L172-L172
CONTRACT_ID: stepN:p11:final-data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: G nonempty
SOURCE_QUANTIFIERS: data
SOURCE_CONCLUSION: A=40 M_C/m>=11, eps_0=m_1 r_0^2/(2^14 A^{2n}), r_0=min{rho/2,32 g/m}, R_0=r_0/A, c_K=(2 pi eps_0/kappa_C)^{1/(2n)}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:constants, bpN:p11:hessian
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:constants | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-data@L172-L172 | Definition constants
EDGE: bpN:p11:hessian | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-data@L172-L172 | A=40 M_C/m>=11 uses m<=M_C
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c
REVIEWER: sol-review-N-f
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: A>=11 is true but weaker than the A>=40 that m<=M_C gives; the later use (Lemma block-data) needs A>=36 M_1/m_1+sqrt 2, which is derived there

NODE: stepN:p11:final-mu
KIND: step
TITLE: The threshold
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-mu@L173-L173
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-mu@L173-L173
CONTRACT_ID: stepN:p11:final-mu
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: G nonempty; gamma_1,gamma_2 of Lemma exponents; the constants
SOURCE_QUANTIFIERS: the fixed data first; choose positive mu_a,...,mu_e and mu_f from final-time, then mu_0=min(mu_a,...,mu_f); for every mu with 0<mu<mu_0
SOURCE_CONCLUSION: mu_0=min{mu_a..mu_f} with mu_a=2 pi eps_0/kappa_C, mu_b=rho^{1/b_n}, mu_c=(pi s c_K/(3 sqrt n))^{2n}, mu_d=(c_K/(256 k rho R_0))^{1/gamma_1}, mu_e=(c_K/R_0)^{1/gamma_2}, mu_f of step final-time; for 0<mu<mu_0: eps<=eps_0, d<=rho, kappa>=6 (B1), K>=256 k rho R_0 mu^{-2 b_n} (B2), R_0/(2K)<=mu^{b_n}/2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:exponents, stepN:p11:final-time, stepN:p11:final-data, bpN:p11:constants, bpN:p11:ext-rpow
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:exponents | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-mu@L173-L173 | gamma_1,gamma_2>0 (Lemma exponents)
EDGE: stepN:p11:final-time | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-mu@L173-L173 | mu_f from step final-time
EDGE: stepN:p11:final-data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-mu@L173-L173 | eps_0, R_0, c_K
EDGE: bpN:p11:constants | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-mu@L173-L173 | kappa_C, s, K(mu), kappa(mu), d
EDGE: bpN:p11:ext-rpow | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-mu@L173-L173 | power rules and monotonicity of mu->mu^gamma
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-delta-N-g
REVIEWER: sol-delta2-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: threshold (KAM/Nekhoroshev/Partial/Threshold.lean)
LEAN_NOTE: audit N11-O PASS WITH NOTES, but threshold gives existential mu0 with the inequalities; explicit mu_a..mu_f formulas and mu_0=min of the node conclusion not stated
NOTE: -

NODE: stepN:p11:final-time
KIND: step
TITLE: Time
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-time@L174-L174
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-time@L174-L174
CONTRACT_ID: stepN:p11:final-time
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p0:partial; branch G nonempty; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: the fixed data first; there exists mu_f>0 depending only on those data such that the time comparison holds for every mu with 0<mu<mu_f
SOURCE_CONCLUSION: T_P=C_T mu^{-1/2}exp(c_2 mu^{-1/(2n)}) with C_T=(s m r_0/(240 M_C (A c_K)^n))(2 pi/kappa_C)>0, c_2=pi s c_K/(3 sqrt n)>0; mu T_P e^{-mu^{-a_n}}>=C_T mu^{1/2}e^{(c_2/2)mu^{-1/(2n)}}->infinity, which defines mu_f
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:block, bpN:p11:constants, bpN:p11:exponents, bpN:p11:ext-rpow, bpN:p0:partial-exponents#partialTimeExponent
EDGE: bpN:p0:partial-exponents#partialTimeExponent | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-time@L174-L174 | direct use of bpN:p0:partial-exponents#partialTimeExponent in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:block | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-time@L174-L174 | T_P=s m_1 r_Theta e^{kappa/6}/(240 M_1 eps) of Theorem block
EDGE: bpN:p11:constants | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-time@L174-L174 | r_Theta, eps, K, kappa in terms of mu; m_1/M_1=m/M_C
EDGE: bpN:p11:exponents | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-time@L174-L174 | a_n<1/(2n)
EDGE: bpN:p11:ext-rpow | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-time@L174-L174 | exp(y)/y^N->infinity and power rules
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-review-N-f
REVIEWER: sol-delta-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: threshold (KAM/Nekhoroshev/Partial/Threshold.lean)
LEAN_NOTE: audit N11-O PASS WITH NOTES, but only the existential blockTime comparison is proved; closed form T_P=C_T mu^{-1/2}exp(c_2 ...) and explicit mu_f not stated
NOTE: -

NODE: stepN:p11:final-given
KIND: step
TITLE: Given $\mu,P,C,z,t$
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-given@L175-L175
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-given@L175-L175
CONTRACT_ID: stepN:p11:final-given
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: mu<mu_0; mu, P, C, z, t given with t in [0,min(C,mu^{-1}exp(mu^{-a_n}))]
SOURCE_QUANTIFIERS: t
SOURCE_CONCLUSION: if t=0 the claim is 0<=mu^{b_n}/2; for t>0: t<=mu^{-1}e^{mu^{-a_n}}<=T_P and [0,t] subset [0,C]
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p11:final-time, stepN:p11:final-mu, bpN:p11:constants, bpN:p0:partial-exponents#partialTimeExponent, bpN:p0:partial-exponents#partialDriftExponent
EDGE: bpN:p11:constants | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-given@L175-L175 | direct use of bpN:p11:constants in the statement or proof at this span
EDGE: bpN:p0:partial-exponents#partialTimeExponent | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-given@L175-L175 | direct package or input used by this proof step
EDGE: bpN:p0:partial-exponents#partialDriftExponent | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-given@L175-L175 | direct package or input used by this proof step
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p11:final-time | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-given@L175-L175 | mu T_P e^{-mu^{-a_n}}>=1 for mu<mu_f gives t<=T_P
EDGE: stepN:p11:final-mu | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-given@L175-L175 | mu<mu_0<=mu_f
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-review-N-f
REVIEWER: sol-delta-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p11:final-orbit
KIND: step
TITLE: The orbit
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-orbit@L176-L176
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-orbit@L176-L176
CONTRACT_ID: stepN:p11:final-orbit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p0:partial; branch G nonempty and t>0; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: z
SOURCE_CONCLUSION: y=Theta o z satisfies y'=F_0(y) with F_0=X^{2pi}_{H-hat_mu} everywhere defined; by Lemma domain(c), sigma F_0=X^{2pi}_{(h-breve+f-breve)^R} on W(I_0,r_0); the slow variables of y lie in core(D,d) on [0,t]
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:orbit, bpN:p11:domain, bpN:p11:block-setting, bpN:p0:sol#IsSolutionOn, bpN:p0:partial-sec#degenerateHamiltonian, bpN:p0:partial-core#innerCore, bpN:p0:partial-sec#fast, bpN:p0:partial-sec#slow, stepN:p11:final-mu, bpN:p11:wfield, bpN:p11:s-real#data, bpN:p3:gen-sol, bpN:p11:constants
EDGE: bpN:p11:wfield | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-orbit@L176-L176 | direct use of bpN:p11:wfield in the statement or proof at this span
EDGE: bpN:p11:s-real#data | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-orbit@L176-L176 | direct use of bpN:p11:s-real#data in the statement or proof at this span
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-orbit@L176-L176 | direct use of bpN:p3:gen-sol in the statement or proof at this span
EDGE: bpN:p11:constants | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-orbit@L176-L176 | direct use of bpN:p11:constants in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:orbit | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-orbit@L176-L176 | Lemma orbit: y=Theta o z has y'=X^{2pi}_{H-hat}(y)
EDGE: bpN:p11:domain | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-orbit@L176-L176 | Lemma domain(c) on W(I_0,r_0)
EDGE: bpN:p11:block-setting | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-orbit@L176-L176 | block-setting (mu<mu_0 secures eps<=eps_0, d<=rho)
EDGE: bpN:p0:sol#IsSolutionOn | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-orbit@L176-L176 | (Z1) IsSolutionOn: two-sided derivative on [0,C]
EDGE: bpN:p0:partial-sec#degenerateHamiltonian | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-orbit@L176-L176 | H_mu of (Z1)
EDGE: bpN:p0:partial-core#innerCore | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-orbit@L176-L176 | I_0=fast(z(0)_2) in core(G,mu^{b_n}) subset G; slow in core(D,mu^{b_n})
EDGE: bpN:p0:partial-sec#fast | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-orbit@L176-L176 | fast(z(0)_2)
EDGE: bpN:p0:partial-sec#slow | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-orbit@L176-L176 | slow variables of y
EDGE: stepN:p11:final-mu | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-orbit@L176-L176 | mu<mu_0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-review-N-f
REVIEWER: sol-delta-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p11:final-sign
KIND: step
TITLE: Sign
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-sign@L177-L177
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-sign@L177-L177
CONTRACT_ID: stepN:p11:final-sign
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p0:partial; branch G nonempty and t>0; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: sigma
SOURCE_CONCLUSION: sigma=+1: Theorem block with F=F_0, J=[0,C], t_1=t; sigma=-1: y-bar(u)=y(-u) on [-C,0] has y-bar'=-F_0(y-bar); -F_0=X^{2pi}_{(h-breve+f-breve)^R} on W(I_0,r_0), Theorem block with F=-F_0, t_1=-t
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:block, stepN:p11:final-orbit, stepN:p11:final-given, bpN:p11:ext-chain, bpN:p11:wfield, bpN:p11:block-setting, bpN:p11:constants
EDGE: bpN:p11:wfield | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-sign@L177-L177 | direct use of bpN:p11:wfield in the statement or proof at this span
EDGE: bpN:p11:block-setting | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-sign@L177-L177 | direct use of bpN:p11:block-setting in the statement or proof at this span
EDGE: bpN:p11:constants | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-sign@L177-L177 | direct use of bpN:p11:constants in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:block | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-sign@L177-L177 | Theorem block
EDGE: stepN:p11:final-orbit | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-sign@L177-L177 | y, F_0 and the identification on W(I_0,r_0)
EDGE: stepN:p11:final-given | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-sign@L177-L177 | t<=T_P, [0,t] subset [0,C]
EDGE: bpN:p11:ext-chain | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-sign@L177-L177 | chain rule for the time-reversed curve y(-u)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-delta-N-g
REVIEWER: sol-delta2-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p11:final-drift
KIND: step
TITLE: Drift
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-drift@L178-L178
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-drift@L178-L178
CONTRACT_ID: stepN:p11:final-drift
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed source data and hypotheses of bpN:p0:partial; branch G nonempty and t>0; prior proof steps are derived through DEPS, not extra assumptions
SOURCE_QUANTIFIERS: t
SOURCE_CONCLUSION: ¦I(t)-I_0¦_inf<=R_0/(2K)<=mu^{b_n}/2, i.e. ¦fast z(t)_2-fast z(0)_2¦<=(1/2)mu^{b_n}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p11:final-sign, stepN:p11:final-mu, bpN:p11:orbit, bpN:p11:constants, bpN:p0:partial-sec#fast, bpN:p0:partial-exponents#partialDriftExponent
EDGE: bpN:p11:constants | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-drift@L178-L178 | direct use of bpN:p11:constants in the statement or proof at this span
EDGE: bpN:p0:partial-sec#fast | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-drift@L178-L178 | direct use of bpN:p0:partial-sec#fast in the statement or proof at this span
EDGE: bpN:p0:partial-exponents#partialDriftExponent | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-drift@L178-L178 | direct use of bpN:p0:partial-exponents#partialDriftExponent in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p11:final-sign | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-drift@L178-L178 | Theorem block gives ¦I(t)-I_0¦_inf<=R_0/(2K)
EDGE: stepN:p11:final-mu | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-drift@L178-L178 | R_0/(2K)<=mu^{b_n}/2 for mu<mu_0
EDGE: bpN:p11:orbit | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-drift@L178-L178 | fast actions unchanged by Theta, so I(t)-I_0=fast z(t)_2-fast z(0)_2
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-review-N-f
REVIEWER: sol-delta-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p11:final-order
KIND: step
TITLE: Quantifier order
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-order@L179-L179
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-order@L179-L179
CONTRACT_ID: stepN:p11:final-order
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the thresholds mu_a..mu_f
SOURCE_QUANTIFIERS: n,k,G,G-prime,D,rho,g,m,M_C,h with their hypotheses; choose mu_0 before universally quantified mu,P,C,z,t
SOURCE_CONCLUSION: mu_0 depends only on (n,k,rho,g,m,M_C) and is chosen before mu,P,C,z,t
CONSTANT_SCOPE: mu_0 depends only on (n,k,rho,g,m,M_C), and is chosen before mu,P,C,z,t
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p11:final-mu, bpN:p11:constants, stepN:p11:final-time
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p11:final-mu | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-order@L179-L179 | mu_0=min{mu_a..mu_f}, each a function of the constants
EDGE: bpN:p11:constants | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-order@L179-L179 | all constants depend only on the data
EDGE: stepN:p11:final-time | blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:final-order@L179-L179 | mu_f depends only on the constants
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-review-N-f
REVIEWER: sol-delta-N-g
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: the step claims dependence on (n,k,rho,g,m,M_C) only, a sub-list of the frozen statement (n,k,G,G',D,rho,g,m,M_C,h); recorded as stated (SPEC). Within p11c, constants of Definition constants do not involve G, G', D, h beyond sigma, which is irrelevant for the thresholds

NODE: bpN:p11:s-real#data
KIND: definition
TITLE: Data of Section s-real: W^e_rho, G^R, G-orbits in W^e_rho
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:s-real#data@L4-L5
PROOF_SOURCE: -
CONTRACT_ID: bpN:p11:s-real#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpN:p11:s-ext-class#data (I_c, S, r_B, s, w, lambda, c, S-tilde); 0<rho<=r_B; G in O(r,s)^{e,R}
SOURCE_QUANTIFIERS: rho; G; interval J
SOURCE_CONCLUSION: defines W^e_rho={(theta,I,x-tilde) in R^{2n+2k}: ¦I-I_c¦<rho, dist_inf(x-tilde,S-tilde)<rho}=D^e_{rho,s} cap R^{2n+2k} (open); G^R=G restricted to W^e_r (0 off it); a G-orbit in W^e_rho on an interval J is y:R->R^{2n+2k} with y(t) in W^e_rho and y'(t)=X^c_{G^R}(y(t)) for t in J, y defined on R and differentiable two-sidedly at every t in J (also at endpoints), exactly as in Part 3 (IsSolIn)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p11:ext-class, bpN:p11:wfield, bpN:p11:s-ext-class#data, bpN:p3:gen-sol, bpN:p4:norm, bpN:p4:domains
EDGE: bpN:p4:norm | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:s-real#data@L4-L5 | direct use of bpN:p4:norm in the statement or proof at this span
EDGE: bpN:p4:domains | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:s-real#data@L4-L5 | direct use of bpN:p4:domains in the statement or proof at this span
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p11:ext-class | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:s-real#data@L4-L5 | D^e_{rho,s}, O^{e,R}, W^e_R
EDGE: bpN:p11:wfield | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:s-real#data@L5-L5 | X^c_{G^R} of Definition wfield
EDGE: bpN:p11:s-ext-class#data | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:s-real#data@L4-L4 | I_c, S-tilde, r_B, lambda, c
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:s-real#data@L5-L5 | the two-sided solution predicate IsSolIn of Part 3 used for orbits
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p11c+sol-review-N-f
REVIEWER: sol-delta-N-g
LEAN_STATUS: PROVED
LEAN_REF: PartialBlock.realDom, realHamiltonianExt, ExtOrbit (KAM/Nekhoroshev/Partial/Setting.lean)
LEAN_NOTE: audit N11-A PASS WITH NOTES; W^e, G^R, G-orbit
NOTE: section-data node for coverage item p11c:prose-L4-L5 (SPEC table); the frozen IsSolutionOn is a comparison (no edge); consumed by real-system, conj, preimage, transfer, nonresonant, energy-free, resonant and block theorem

NODE: bpN:p11:hessian#real-hessian
KIND: step
TITLE: Real and complex Hessians on the partial-theorem tube
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:hessian@L126-L126
PROOF_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#stepN:p11:hs-op@L129-L129
CONTRACT_ID: bpN:p11:hessian#real-hessian
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed data and hypotheses of bpN:p0:partial; h holomorphic and complex C^2 on the open G-prime_rho, real on its real slice; no centred-ball IsAnalyticIntegrable premise
SOURCE_QUANTIFIERS: the fixed partial-theorem data; every real I in the real slice U of G-prime_rho
SOURCE_CONCLUSION: the real derivatives of h_R at I are restrictions of the complex derivatives; Q(I)=D^2 h_R(I)=Q_C(I), symmetric and real, and omega(I) is the real gradient
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p0:actionnbhd#actionNbhd, bpN:p0:realpart#realPart, bpN:p0:freq#frequencyMap
EDGE: bpN:p0:actionnbhd#actionNbhd | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:hessian@L126-L126 | real slice, real restriction and frequency used in this bridge
EDGE: bpN:p0:realpart#realPart | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:hessian@L126-L126 | real slice, real restriction and frequency used in this bridge
EDGE: bpN:p0:freq#frequencyMap | blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:hessian@L126-L126 | real slice, real restriction and frequency used in this bridge
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: new+sol-review-N-f
REVIEWER: sol-delta4-N-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: L115 cites bpN:p1:holo-real, stated for centred action balls with the Part 1 analytic-integrable/perturbation data. Those premises are not supplied here. This step exposes the arbitrary-open-tube real-Hessian identification actually used; it is not a proof or an extra assumption of the frozen theorem.

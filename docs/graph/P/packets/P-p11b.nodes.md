NODE: bpP:p11b:e-ode
KIND: external
TITLE: Analytic ODE
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:e-ode@L20-L20
PROOF_SOURCE: -
CONTRACT_ID: bpP:p11b:e-ode
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a real-analytic vector field (possibly depending on parameters) with an open domain of definition of its flow
SOURCE_QUANTIFIERS: the vector field and parameters; initial data and time in the open domain
SOURCE_CONCLUSION: the flow depends real-analytically on time, initial data and parameters on its (open) domain of definition
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: standard external; existence, uniqueness and continuation are the imports bpN:p3:gen-continuation and bpN:p3:gen-uniqueness (the item cites N local-exist for them), the analytic dependence on parameters is the added content, so the item is kept as an external

NODE: bpP:p11b:e-ca
KIND: external
TITLE: Finite exact computation
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:e-ca@L23-L23
PROOF_SOURCE: -
CONTRACT_ID: bpP:p11b:e-ca
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a polynomial or rational identity with rational coefficients, in finitely many variables, of bounded degree
SOURCE_QUANTIFIERS: the identity, its finitely many variables and degree bound
SOURCE_CONCLUSION: it is verified by a finite exact computation (Lean: ring, field_simp, norm_num); includes the displayed expansions of Lemma orbit and the identities of Proposition pair-jet and Theorem quartic-explicit (generated with a CAS and checked numerically in sec-num; the numerical generation is provenance)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: kept as a track-P external (SPEC); the CAS and numerical generation (sec-num) is provenance, not a proof ingredient

NODE: bpP:p11b:sec-set#data
KIND: definition
TITLE: Setting of Part 11b (n=2 data and the objects of Parts 7-9, abbreviations, complex notation, slow variables)
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:sec-set#data@L14-L16
PROOF_SOURCE: -
CONTRACT_ID: bpP:p11b:sec-set#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n=2; G, m0>0, kappa=G m0; m=(m_1,m_2) in (0,inf)^2; the objects of Parts 7-9 as named (chart Psi, secular functions, Q_h, sigma, rho, Phi_4, NR_4, Laplace coefficients)
SOURCE_QUANTIFIERS: G, m0, m_1, m_2; then a in A_2
SOURCE_CONCLUSION: fixes w=(lambda,xi,Lambda,eta), u_i=(xi_i,eta_i) in R^2, a_i=Lambda_i^2/(m_i^2 kappa), A_2={0<a_1<a_2} (increasing order), alpha=a_1/a_2 in (0,1), S_fix, S_mov and their common jet (Corollary same-jets), C_0, a_12, b_12, Q_h, eigenvalues sigma_1<sigma_2<0 and rotation rho in SO(2), Phi_4, NR_4, Laplace coefficients b_s^(k); abbreviations beta_0=b_{1/2}^(0)(alpha), beta_1=b_{1/2}^(1)(alpha), Delta=1-alpha^2, pref=-G m_1 m_2/a_2; complex notation zeta=v_0+i v_1 for an eccentricity vector, X=e^{i lambda}; slow variables z=(z_1,z_2), z_j=(x_j,y_j), R_j=(x_j^2+y_j^2)/2 with the chart form dLambda^dlambda+dy^dx, bracket {F,G}:=dF(X_G) with X_G of the frozen sign convention (xdot=dG/dy, ydot=-dG/dx); dictionary q=x, p=y (position xi, momentum eta)
CONSTANT_SCOPE: none (G, m0, m fixed first; kappa=G m0)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p8:conv#data, bpP:p7:product-def, bpP:p8:coeffs, bpP:p9:n2, bpP:p9:local-analytic, bpP:p9:good, bpP:p8:laplace-def, bpP:p8:laplace, bpP:p8:same-jets, bpP:p7:poincare-def
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p8:conv#data | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:sec-set#data@L14-L14 | chart, w, u_i, a_i, S_fix, S_mov, averages of Part 8
EDGE: bpP:p7:product-def | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:sec-set#data@L14-L14 | the chart Psi=Psi^(2) and the coordinates w
EDGE: bpP:p8:coeffs | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:sec-set#data@L14-L14 | C_0, a_12, b_12, Q_h of Definition coeffs
EDGE: bpP:p9:n2 | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:sec-set#data@L14-L14 | sigma_1<sigma_2<0 and the rotation rho in SO(2) of Corollary n2
EDGE: bpP:p9:local-analytic | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:sec-set#data@L14-L14 | rotation rho of Proposition local-analytic
EDGE: bpP:p9:good | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:sec-set#data@L14-L14 | Phi_4 and NR_4 of Definition good
EDGE: bpP:p8:laplace-def | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:sec-set#data@L14-L14 | Laplace coefficients b_s^(k)
EDGE: bpP:p8:laplace | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:sec-set#data@L14-L14 | analyticity and series of the Laplace coefficients
EDGE: bpP:p8:same-jets | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:sec-set#data@L14-L14 | common jet of S_fix and S_mov; sign convention of X_G (part (b)) at L16
EDGE: bpP:p7:poincare-def | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:sec-set#data@L16-L16 | eccentricity vector v and its complex form zeta of the Poincare chart
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: audit T1 PASS WITH NOTES but T1 defines only PlanarData, axes/actions dictionaries, hat functions, secular average, slow length, quartic; Laplace coefficients, sigma, rho, Phi_4, NR_4 etc. are not defined here
NOTE: created from p11b:prose-L14-L16 (SPEC section data); consumers: nearly every node of Part 11b

NODE: bpP:p11b:orbit
KIND: lemma
TITLE: Kepler expansion to order four
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:orbit@L28-L36
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:orbit@L37-L41
CONTRACT_ID: bpP:p11b:orbit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the Poincare chart with a=1 (Definition bpP:p7:poincare-def); z_orb=q_0+i q_1 for the position q; X=e^{i lambda}, lambda the mean longitude
SOURCE_QUANTIFIERS: formal power series in (zeta, zeta-bar) with coefficients Laurent polynomials in X; for the analyticity clause: lambda fixed, v with ¦v¦<1
SOURCE_CONCLUSION: z_orb = X + (X^2 zbar/2 - 3 zeta/2) + (3 X^3 zbar^2/8 - X zeta zbar/2 + X^(-1) zeta^2/8) + (X^4 zbar^3/3 - 3 X^2 zeta zbar^2/8 + X^(-2) zeta^3/24) + (125 X^5 zbar^4/384 - 3 X^3 zeta zbar^3/8 - X zeta^2 zbar^2/64 + X^(-1) zeta^3 zbar/24 + 3 X^(-3) zeta^4/128) + O(¦zeta¦^5), grouped by degree 1..4; z_orb at fixed lambda is real analytic in v for ¦v¦<1 and its degree-d homogeneous part is the d-th Taylor polynomial
CONSTANT_SCOPE: numerical rational coefficients only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p11b:or-kep, stepP:p11b:or-pos, stepP:p11b:or-an, bpP:p7:poincare-def, bpP:p11b:sec-set#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p11b:or-kep | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:orbit@L38-L38 | proof step: Kepler equation, series of the eccentric anomaly
EDGE: stepP:p11b:or-pos | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:orbit@L39-L39 | proof step: position, the displayed table
EDGE: stepP:p11b:or-an | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:orbit@L40-L40 | proof step: analyticity
EDGE: bpP:p7:poincare-def | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:orbit@L29-L29 | the Poincare chart with a=1
EDGE: bpP:p11b:sec-set#data | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:orbit@L29-L29 | complex notation zeta, X
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p11b:or-kep
KIND: step
TITLE: Kepler's equation
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:or-kep@L38-L38
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:or-kep@L38-L38
CONTRACT_ID: stepP:p11b:or-kep
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Kepler equation F-v_0 sin F+v_1 cos F=lambda (Proposition bpP:p7:regular-kepler(a)); F=lambda+phi, E=e^{iF}=X e^{i phi}
SOURCE_QUANTIFIERS: lambda; v; formal degree d
SOURCE_CONCLUSION: phi=Im(zeta-bar E)=(zeta-bar E-zeta E-bar)/(2i), a fixed-point equation with right side divisible by zeta, zeta-bar; Picard iteration from phi=0 fixes phi modulo degree d after d steps (a finite polynomial computation)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p7:regular-kepler, bpP:p11b:e-ca, bpP:p11b:sec-set#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p7:regular-kepler | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:or-kep@L38-L38 | Kepler equation of the regular chart
EDGE: bpP:p11b:e-ca | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:or-kep@L38-L38 | the iteration is a finite polynomial computation
EDGE: bpP:p11b:sec-set#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:or-kep@L38-L38 | zeta, X notation
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p11b:or-pos
KIND: step
TITLE: Position
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:or-pos@L39-L39
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:or-pos@L39-L39
CONTRACT_ID: stepP:p11b:or-pos
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: chart formula q=a(k c-v+(v.c)/(1+k) v) with a=1, k=sqrt(1-¦zeta¦^2), v.c=Re(zeta-bar E), c<->E; the series of phi
SOURCE_QUANTIFIERS: lambda; zeta formal; degree <=4
SOURCE_CONCLUSION: z_orb=k E-zeta+Re(zeta-bar E)/(1+k) zeta; inserting the series of phi, k and (1+k)^(-1) and collecting gives the displayed table through degree 4
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p7:poincare-def, stepP:p11b:or-kep, bpP:p11b:e-ca, bpP:p11b:sec-set#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p7:poincare-def | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:or-pos@L39-L39 | position formula q of the chart
EDGE: stepP:p11b:or-kep | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:or-pos@L39-L39 | the series of phi=F-lambda
EDGE: bpP:p11b:e-ca | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:or-pos@L39-L39 | expansion and collection is a finite exact computation (the table is of this kind)
EDGE: bpP:p11b:sec-set#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:or-pos@L39-L39 | zeta, X notation
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p11b:or-an
KIND: step
TITLE: Analyticity
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:or-an@L40-L40
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:or-an@L40-L40
CONTRACT_ID: stepP:p11b:or-an
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Proposition bpP:p7:regular-kepler(a): F analytic in v for ¦v¦<1; the formulas above
SOURCE_QUANTIFIERS: lambda fixed; v with ¦v¦<1
SOURCE_CONCLUSION: z_orb is analytic in v for ¦v¦<1 and the Taylor polynomials are the homogeneous parts of its formal series
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p7:regular-kepler, stepP:p11b:or-pos
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p7:regular-kepler | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:or-an@L40-L40 | analyticity of F in v
EDGE: stepP:p11b:or-pos | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:or-an@L40-L40 | the formulas for z_orb
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p11b:laplace-red
KIND: lemma
TITLE: Laplace coefficients: relations and reduction to two functions
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:laplace-red@L43-L56
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:laplace-red@L57-L62
CONTRACT_ID: bpP:p11b:laplace-red
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: s in R, k>=0, alpha in (0,1) (circular denominator 1+alpha^2-2 alpha cos t>0), b_s^(k)=b_s^(k)(alpha) of Definition bpP:p8:laplace-def, b_s^(-k)=b_s^(k); divisors (s-1)alpha, s alpha, s-1-k guarded where relations are solved
SOURCE_QUANTIFIERS: s, k, alpha; then s in 1/2+N, k in N for the reduction
SOURCE_CONCLUSION: (R1) b_{s-1}^(k)=(1+alpha^2) b_s^(k)-alpha(b_s^(k+1)+b_s^(k-1)); (R2) k b_{s-1}^(k)=(s-1) alpha (b_s^(k-1)-b_s^(k+1)); (R3) (s-1-k) alpha b_s^(k+1)=(k+s-1) alpha b_s^(k-1)-k(1+alpha^2) b_s^(k) for k>=1; for s in 1/2+N, k in N, b_s^(k)=r^(0)_{s,k}(alpha) beta_0+r^(1)_{s,k}(alpha) beta_1 with rational r in Q(alpha) (denominators dividing alpha^k Delta^(2(s-1/2)) times linear factors not vanishing for half-integer s); explicitly b_{s+1}^(0)=((1+alpha^2) b_s^(0)+2 alpha(1-1/s) b_s^(1))/Delta^2, b_{s+1}^(1)=((1+alpha^2)(1-1/s) b_s^(1)+2 alpha b_s^(0))/Delta^2, b_{s+1}^(k+1)=b_{s+1}^(k-1)-k b_s^(k)/(s alpha) for k>=1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p11b:lr-1, stepP:p11b:lr-2, stepP:p11b:lr-3, stepP:p11b:lr-red, bpP:p8:laplace-def, bpP:p11b:sec-set#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p11b:lr-1 | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:laplace-red@L58-L58 | proof step (R1)
EDGE: stepP:p11b:lr-2 | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:laplace-red@L59-L59 | proof step (R2)
EDGE: stepP:p11b:lr-3 | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:laplace-red@L60-L60 | proof step (R3)
EDGE: stepP:p11b:lr-red | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:laplace-red@L61-L61 | proof step: reduction to beta_0, beta_1
EDGE: bpP:p8:laplace-def | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:laplace-red@L44-L44 | the coefficients b_s^(k)
EDGE: bpP:p11b:sec-set#data | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:laplace-red@L50-L50 | beta_0, beta_1, Delta
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p11b:lr-1
KIND: step
TITLE: (R1)
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:lr-1@L58-L58
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:lr-1@L58-L58
CONTRACT_ID: stepP:p11b:lr-1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: b_s^(k)=(2pi)^(-1) int cos(kt) Delta_t^(-s) dt with Delta_t=1+alpha^2-2 alpha cos t
SOURCE_QUANTIFIERS: s, k, alpha
SOURCE_CONCLUSION: (R1): from Delta_t Delta_t^(-s)=Delta_t^(-(s-1)) and 2 cos t cos kt=cos(k+1)t+cos(k-1)t
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p8:laplace-def
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p8:laplace-def | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:lr-1@L58-L58 | integral definition of b_s^(k)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p11b:lr-2
KIND: step
TITLE: (R2)
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:lr-2@L59-L59
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:lr-2@L59-L59
CONTRACT_ID: stepP:p11b:lr-2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: b_s^(k) integral definition; int_0^{2pi} d/dt(sin kt Delta_t^(-(s-1))) dt=0
SOURCE_QUANTIFIERS: s, k, alpha
SOURCE_CONCLUSION: (R2): k b_{s-1}^(k)=(s-1) alpha (b_s^(k-1)-b_s^(k+1)) using 2 sin kt sin t=cos(k-1)t-cos(k+1)t
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p8:laplace-def
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p8:laplace-def | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:lr-2@L59-L59 | integral definition of b_s^(k)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p11b:lr-3
KIND: step
TITLE: (R3)
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:lr-3@L60-L60
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:lr-3@L60-L60
CONTRACT_ID: stepP:p11b:lr-3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (R1) and (R2)
SOURCE_QUANTIFIERS: s, k>=1, alpha
SOURCE_CONCLUSION: (R3) by eliminating b_{s-1}^(k) between (R1) and (R2)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p11b:lr-1, stepP:p11b:lr-2
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p11b:lr-1 | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:lr-3@L60-L60 | (R1)
EDGE: stepP:p11b:lr-2 | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:lr-3@L60-L60 | (R2)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p11b:lr-red
KIND: step
TITLE: Reduction
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:lr-red@L61-L61
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:lr-red@L61-L61
CONTRACT_ID: stepP:p11b:lr-red
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (R1)-(R3); beta_0=b_{1/2}^(0), beta_1=b_{1/2}^(1)
SOURCE_QUANTIFIERS: s in 1/2+N, k in N
SOURCE_CONCLUSION: at s=1/2 (R3) gives all b_{1/2}^(k) from beta_0, beta_1; the step s->s+1 solves a 2x2 system of determinant Delta^2 obtained from (R1) at s+1 for k=0,1 and (R2), giving the displayed formulas; induct on s and k
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p11b:lr-3, stepP:p11b:lr-2, stepP:p11b:lr-1, bpP:p11b:sec-set#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p11b:lr-3 | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:lr-red@L61-L61 | (R3) at s=1/2
EDGE: stepP:p11b:lr-2 | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:lr-red@L61-L61 | (R2) at s+1
EDGE: stepP:p11b:lr-1 | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:lr-red@L61-L61 | (R1) at s+1 for k=0,1
EDGE: bpP:p11b:sec-set#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:lr-red@L61-L61 | beta_0, beta_1, Delta
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p11b:pair-jet
KIND: proposition
TITLE: The jet of $\mathcal W$ to order four, by Fourier averaging
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:pair-jet@L64-L91
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:pair-jet@L92-L98
CONTRACT_ID: bpP:p11b:pair-jet
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<alpha<1; W(alpha;v_1,v_2)=(2pi)^(-2) int int ¦alpha z_orb(lambda_1;zeta_1)-z_orb(lambda_2;zeta_2)¦^(-1) d lambda_1 d lambda_2 of Proposition bpP:p8:quartic(a) (S_12=-G m_1 m_2 a_2^(-1) W; v_i eccentricity vector of planet i, zeta_i its complex form); beta_0, beta_1, Delta as in the setting
SOURCE_QUANTIFIERS: alpha in (0,1); v near 0
SOURCE_CONCLUSION: W is real analytic near v=0 with W=W_0+W_2+W_4+O(¦v¦^6), W_0=beta_0, W_2=A¦zeta_1¦^2+A¦zeta_2¦^2+B Re(zeta_1-bar zeta_2), W_4=p_1¦zeta_1¦^4+p_2¦zeta_2¦^4+p_3¦zeta_1¦^2¦zeta_2¦^2+p_4 Re(zeta_1-bar zeta_2)^2+p_5¦zeta_1¦^2 Re(zeta_1-bar zeta_2)+p_6¦zeta_2¦^2 Re(zeta_1-bar zeta_2) with the explicit rational expressions A, B, p_1..p_6 in alpha, beta_0, beta_1, Delta displayed in the statement (A=(1/4)alpha b_{3/2}^(1), B=-(1/2)alpha b_{3/2}^(2)); the same coefficient of ¦zeta_1¦^2 and ¦zeta_2¦^2 and the vanishing of all further monomials; the power series in alpha of A, B, p_1..p_6 (convergent for ¦alpha¦<1)
CONSTANT_SCOPE: none (coefficients depend on alpha only)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p11b:pj-formal, stepP:p11b:pj-bin, stepP:p11b:pj-avg, stepP:p11b:pj-red, stepP:p11b:pj-cons, bpP:p8:quartic, bpP:p8:laplace, bpP:p11b:sec-set#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p11b:pj-formal | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:pair-jet@L93-L93 | proof step: reduction to a formal series
EDGE: stepP:p11b:pj-bin | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:pair-jet@L94-L94 | proof step: binomial expansion
EDGE: stepP:p11b:pj-avg | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:pair-jet@L95-L95 | proof step: averaging rule
EDGE: stepP:p11b:pj-red | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:pair-jet@L96-L96 | proof step: reduction and extraction
EDGE: stepP:p11b:pj-cons | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:pair-jet@L97-L97 | proof step: the identities A, B in terms of b_{3/2}^(1), b_{3/2}^(2)
EDGE: bpP:p8:quartic | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:pair-jet@L65-L65 | W and S_12 of Proposition quartic(a)
EDGE: bpP:p8:laplace | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:pair-jet@L81-L81 | convergence of the power series in alpha
EDGE: bpP:p11b:sec-set#data | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:pair-jet@L65-L65 | zeta_i, v_i, beta_0, beta_1, Delta
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: the displayed power series (eq:series) are inserted from the Laplace series (pj-red); the source citation of Theorem quadratic-form (L90) is provenance

NODE: stepP:p11b:pj-formal
KIND: step
TITLE: Reduction to a formal series
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:pj-formal@L93-L93
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:pj-formal@L93-L93
CONTRACT_ID: stepP:p11b:pj-formal
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: z_1=alpha z_orb(lambda_1;zeta_1)=alpha X_1+alpha delta_1, z_2=z_orb(lambda_2;zeta_2)=X_2+delta_2 with delta_i=z_orb-X_i of degree >=1; integrand analytic in v for lambda in the compact torus
SOURCE_QUANTIFIERS: lambda_1, lambda_2; v near 0
SOURCE_CONCLUSION: the Taylor coefficients of the average at v=0 are the averages of the Taylor coefficients of the integrand, so it suffices to expand ¦z_1-z_2¦^(-1) formally in (zeta_i, zeta_i-bar) via Lemma orbit and average the coefficients
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p8:perturbation-analytic, bpP:p8:e-diff, bpP:p11b:orbit, bpP:p11b:sec-set#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p8:perturbation-analytic | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:pj-formal@L93-L93 | analytic dependence and differentiation of the average
EDGE: bpP:p8:e-diff | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:pj-formal@L93-L93 | differentiation under the integral over the torus
EDGE: bpP:p11b:orbit | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:pj-formal@L93-L93 | formal expansion of z_orb
EDGE: bpP:p11b:sec-set#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:pj-formal@L93-L93 | zeta_i, X_i
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p11b:pj-bin
KIND: step
TITLE: Binomial expansion
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:pj-bin@L94-L94
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:pj-bin@L94-L94
CONTRACT_ID: stepP:p11b:pj-bin
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the formal setting of the previous step; s=1+alpha^2-2 alpha cos(lambda_1-lambda_2)>0, D=conj(alpha X_1-X_2) d+(alpha X_1-X_2) d-bar+d d-bar with d=alpha delta_1-delta_2
SOURCE_QUANTIFIERS: formal degree d<=4
SOURCE_CONCLUSION: ¦z_1-z_2¦^(-1)=sum_{l=0}^4 binom(-1/2,l) s^(-1/2-l) D^l modulo degree 5; the degree-d coefficient is sum_{l<=d} s^(-1/2-l) L_{d,l}(X_1,X_2;alpha) with L_{d,l} a Laurent polynomial in X_1, X_2 with coefficients polynomial in alpha and in the monomials of zeta_i, zeta_i-bar
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p11b:orbit, stepP:p11b:pj-formal, bpP:p11b:sec-set#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p11b:orbit | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:pj-bin@L94-L94 | delta_i are Laurent polynomials in X_i at each degree
EDGE: stepP:p11b:pj-formal | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:pj-bin@L94-L94 | the formal reduction
EDGE: bpP:p11b:sec-set#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:pj-bin@L94-L94 | Uses X_i=e^{i lambda_i} and the complex orbit notation of the section data.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b+sol-review-P-m
REVIEWER: sol-delta-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p11b:pj-avg
KIND: step
TITLE: Averaging rule
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:pj-avg@L95-L95
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:pj-avg@L95-L95
CONTRACT_ID: stepP:p11b:pj-avg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: s depends on lambda_1-lambda_2 only; X_1^p X_2^r=e^{ip(lambda_1-lambda_2)} e^{i(p+r) lambda_2}
SOURCE_QUANTIFIERS: p, r in Z; s>0
SOURCE_CONCLUSION: the average of X_1^p X_2^r s^(-s) is delta_{p+r,0} b_s^(¦p¦)(alpha) (the lambda_2 integral kills the monomial unless p+r=0; (2pi)^(-1) int e^{ip theta} s^(-s) d theta=b_s^(¦p¦))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p8:laplace-def, bpP:p11b:sec-set#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p8:laplace-def | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:pj-avg@L95-L95 | (2pi)^(-1) int e^{ip theta} (1+alpha^2-2 alpha cos theta)^(-s) d theta=b_s^(¦p¦)
EDGE: bpP:p11b:sec-set#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:pj-avg@L95-L95 | Uses X_i=e^{i lambda_i} and the angle/complex-variable convention directly.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b+sol-review-P-m
REVIEWER: sol-delta-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p11b:pj-red
KIND: step
TITLE: Reduction and extraction
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:pj-red@L96-L96
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:pj-red@L96-L96
CONTRACT_ID: stepP:p11b:pj-red
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the degree-d coefficients of the binomial expansion averaged by the averaging rule; every b_s^(k) occurring has s in {1/2..9/2}, k<=8
SOURCE_QUANTIFIERS: degree 0,2,4
SOURCE_CONCLUSION: each b_s^(k) is a rational combination of beta_0, beta_1; the average is a polynomial in zeta_i, zeta_i-bar of degrees 0,2,4 (odd degrees vanish by (S1)), invariant under rotation (S2) and conjugation (S3), spanned by the six listed monomials; reading off coefficients gives A, B, p_1..p_6 (finite exact computation); the series in alpha follow by inserting the Laplace series of beta_0, beta_1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p11b:pj-bin, stepP:p11b:pj-avg, bpP:p11b:laplace-red, bpP:p8:symmetries, bpP:p11b:e-ca, bpP:p8:laplace, bpP:p11b:sec-set#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p11b:pj-bin | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:pj-red@L96-L96 | the coefficients L_{d,l} to be averaged
EDGE: stepP:p11b:pj-avg | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:pj-red@L96-L96 | the averaging rule
EDGE: bpP:p11b:laplace-red | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:pj-red@L96-L96 | reduction of every b_s^(k) to beta_0, beta_1
EDGE: bpP:p8:symmetries | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:pj-red@L96-L96 | (S1) odd degrees vanish, (S2) rotation invariance, (S3) conjugation invariance
EDGE: bpP:p11b:e-ca | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:pj-red@L96-L96 | finite exact computation reading off the coefficients
EDGE: bpP:p8:laplace | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:pj-red@L96-L96 | Laplace series of beta_0, beta_1 giving eq:series
EDGE: bpP:p11b:sec-set#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:pj-red@L96-L96 | Uses beta_0, beta_1 and zeta_i of the section data directly.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b+sol-review-P-m
REVIEWER: sol-delta-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p11b:pj-cons
KIND: step
TITLE: Consistency with Part 8
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:pj-cons@L97-L97
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:pj-cons@L97-L97
CONTRACT_ID: stepP:p11b:pj-cons
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: A and B are the displayed rational expressions from pj-red; the Laplace reduction of laplace-red is available
SOURCE_QUANTIFIERS: alpha in (0,1)
SOURCE_CONCLUSION: the displayed A and B equal (1/4)alpha b_{3/2}^(1) and -(1/2)alpha b_{3/2}^(2) identically in alpha by the reduction (finite check); comparison with the quadratic part of Theorem quadratic-form and the multipole test are consistency checks
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p11b:pj-red, bpP:p11b:laplace-red, bpP:p11b:e-ca
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p11b:pj-red | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:pj-cons@L97-L97 | the closed forms of A, B
EDGE: bpP:p11b:laplace-red | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:pj-cons@L97-L97 | reduction of b_{3/2}^(1), b_{3/2}^(2) to beta_0, beta_1
EDGE: bpP:p11b:e-ca | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:pj-cons@L97-L97 | identities hold identically in alpha by a finite check
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b+sol-review-P-m
REVIEWER: sol-delta-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: the comparison with Theorem quadratic-form and the multipole expansion are consistency checks (not edges)

NODE: bpP:p11b:quartic-explicit
KIND: theorem
TITLE: The six quartic coefficients
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:quartic-explicit@L100-L109
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:quartic-explicit@L110-L116
CONTRACT_ID: bpP:p11b:quartic-explicit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a in A_2; Lambda_i=m_i sqrt(kappa a_i); alpha=a_1/a_2; A, B, p_nu of Proposition pair-jet; pref=-G m_1 m_2/a_2
SOURCE_QUANTIFIERS: a in A_2 (G, m0, m_1, m_2 fixed)
SOURCE_CONCLUSION: c_1=pref (p_1-A/4)/Lambda_1^2, c_2=pref (p_2-A/4)/Lambda_2^2, c_3=pref p_3/(Lambda_1 Lambda_2), c_4=pref p_4/(Lambda_1 Lambda_2), c_5=pref (p_5-B/8)/(Lambda_1^(3/2) Lambda_2^(1/2)), c_6=pref (p_6-B/8)/(Lambda_1^(1/2) Lambda_2^(3/2)) are real analytic on A_2 and the degree-four part of S_fix and of S_mov in (xi,eta) is Q_4(u)=c_1¦u_1¦^4+c_2¦u_2¦^4+c_3¦u_1¦^2¦u_2¦^2+c_4(u_1.u_2)^2+c_5¦u_1¦^2(u_1.u_2)+c_6¦u_2¦^2(u_1.u_2); thus c_nu^{12}=c_nu in Proposition quartic, and c_1, c_2 coincide with the diagonal formula of Proposition quartic(b)
CONSTANT_SCOPE: c_nu are functions of a (and of G, m0, m_1, m_2) only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p11b:qe-conv, stepP:p11b:qe-an, stepP:p11b:qe-c12, bpP:p11b:pair-jet, bpP:p8:quartic, bpP:p8:same-jets, bpP:p11b:sec-set#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p11b:qe-conv | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:quartic-explicit@L111-L111 | proof step: exact conversion
EDGE: stepP:p11b:qe-an | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:quartic-explicit@L114-L114 | proof step: analyticity and the jet
EDGE: stepP:p11b:qe-c12 | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:quartic-explicit@L115-L115 | proof step: c_1, c_2
EDGE: bpP:p11b:pair-jet | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:quartic-explicit@L106-L106 | A, B, p_nu and S_12=pref W
EDGE: bpP:p8:quartic | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:quartic-explicit@L108-L108 | c_nu^{12} and the diagonal formula (b)
EDGE: bpP:p8:same-jets | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:quartic-explicit@L106-L106 | S_mov has the same degree-four part as S_fix
EDGE: bpP:p11b:sec-set#data | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:quartic-explicit@L101-L101 | A_2, Lambda_i, alpha, pref
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p11b:qe-conv
KIND: step
TITLE: Exact conversion
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:qe-conv@L111-L113
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:qe-conv@L111-L113
CONTRACT_ID: stepP:p11b:qe-conv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: v_i=sqrt((1-Gamma_i/(2 Lambda_i))/Lambda_i) u_i with Gamma_i=¦u_i¦^2/2; w_i=u_i/sqrt(Lambda_i); W_2+W_4 of Proposition pair-jet with ¦zeta_i¦=¦v_i¦, Re(zeta_1-bar zeta_2)=v_1.v_2
SOURCE_QUANTIFIERS: u_1, u_2 near 0; a in A_2
SOURCE_CONCLUSION: v_i=w_i(1-¦w_i¦^2/8+O(¦w¦^4)), so ¦v_i¦^2=¦w_i¦^2-¦w_i¦^4/4+O(¦w¦^6), v_1.v_2=w_1.w_2(1-¦w_1¦^2/8-¦w_2¦^2/8)+O(¦w¦^6); the degree-four part in w of W_2+W_4 is W_4(w)-(A/4)(¦w_1¦^4+¦w_2¦^4)-(B/8)(w_1.w_2)(¦w_1¦^2+¦w_2¦^2); multiplying by pref and converting w to u gives the displayed c_nu
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p11b:pair-jet, bpP:p7:poincare-def, bpP:p8:conv#data, bpP:p11b:sec-set#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p11b:pair-jet | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:qe-conv@L111-L111 | W_2, W_4 and the identification of zeta_i with v_i
EDGE: bpP:p7:poincare-def | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:qe-conv@L111-L111 | v=sqrt((1-Gamma/(2 Lambda))/Lambda)(xi,eta) of the chart
EDGE: bpP:p8:conv#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:qe-conv@L111-L111 | Gamma_i=¦u_i¦^2/2
EDGE: bpP:p11b:sec-set#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:qe-conv@L111-L111 | pref, A_2, Lambda_i
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p11b:qe-an
KIND: step
TITLE: Analyticity and the jet
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:qe-an@L114-L114
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:qe-an@L114-L114
CONTRACT_ID: stepP:p11b:qe-an
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: beta_0, beta_1, Lambda_i real analytic on A_2; Delta^4=(1-alpha^2)^4 nonvanishing; Proposition quartic structure; Corollary same-jets
SOURCE_QUANTIFIERS: a in A_2
SOURCE_CONCLUSION: c_1..c_6 are real analytic on A_2; S_fix and S_mov have the same degree-four part, equal to that of S_12 (pair decomposition)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p8:laplace, bpP:p8:quartic, bpP:p8:same-jets, stepP:p8:qf-pair, bpP:p11b:sec-set#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p8:laplace | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:qe-an@L114-L114 | beta_0, beta_1 real analytic on A_2
EDGE: bpP:p8:quartic | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:qe-an@L114-L114 | structure of the degree-four part
EDGE: bpP:p8:same-jets | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:qe-an@L114-L114 | S_mov and S_fix share the jet
EDGE: stepP:p8:qf-pair | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:qe-an@L114-L114 | pair decomposition S_fix=sum S_ij
EDGE: bpP:p11b:sec-set#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:qe-an@L114-L114 | A_2, beta_0, beta_1, Delta
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p11b:qe-c12
KIND: step
TITLE: $c_1,c_2$
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:qe-c12@L115-L115
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:qe-c12@L115-L115
CONTRACT_ID: stepP:p11b:qe-c12
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: zeta_2=0: the pair average is a function of E=¦v_1¦^2 alone, W(alpha;zeta_1,0)=beta_0+A E+p_1 E^2+...; Step qf-diag gives S_12 at u_2=0 as -G m_1 m_2[h(0)+h2(0) E/4+h4(0) E^2/64+O(E^3)]
SOURCE_QUANTIFIERS: a in A_2; i=1, 2
SOURCE_CONCLUSION: pref A=-G m_1 m_2 h2(0)/4 and pref p_1=-G m_1 m_2 h4(0)/64, hence pref(p_1-A/4)/Lambda_1^2 is the formula of Proposition quartic(b) for c_1; the case i=2 is the same with the outer planet eccentric
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p8:qf-diag, bpP:p8:quartic, bpP:p11b:pair-jet, bpP:p11b:sec-set#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p8:qf-diag | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:qe-c12@L115-L115 | S_12 at u_2=0 in terms of h and E (both orderings)
EDGE: bpP:p8:quartic | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:qe-c12@L115-L115 | formula (b) for c_1, c_2
EDGE: bpP:p11b:pair-jet | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:qe-c12@L115-L115 | W(alpha;zeta_1,0)=beta_0+A E+p_1 E^2
EDGE: bpP:p11b:sec-set#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:qe-c12@L115-L115 | pref
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p11b:sec-bnf#data
KIND: definition
TITLE: Setting of the Birkhoff normalisation (open set of actions, non-resonant Omega, N_0, quartic families, rotation action)
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:sec-bnf#data@L120-L124
PROOF_SOURCE: -
CONTRACT_ID: bpP:p11b:sec-bnf#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: O subset R^2 open set of actions; Omega=(Omega_1,Omega_2): O -> R^2 real analytic with NR_4(Omega): k.Omega(Lambda)!=0 for all k in Z^2, 0<¦k¦_1<=4, Lambda in O
SOURCE_QUANTIFIERS: O, Omega; then Lambda in O, z in R^4, theta in R^2
SOURCE_CONCLUSION: defines N_0(Lambda,z)=sum_j Omega_j(Lambda) R_j(z); a quartic family F(Lambda,z)=sum_{¦gamma¦=4} f_gamma(Lambda) z^gamma with real-analytic f_gamma and real values (monomials in x_1,y_1,x_2,y_2); identification z_j<->x_j+i y_j; rotation action T_theta z=(e^{-i theta_1} z_1, e^{-i theta_2} z_2), which by the frozen sign convention is the flow of N_0: psi^t_{N_0}=T_{t Omega}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p11b:sec-set#data, bpP:p9:good
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p11b:sec-set#data | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:sec-bnf#data@L124-L124 | R_j, z=(z_1,z_2), the bracket and the frozen sign convention xdot=dG/dy, ydot=-dG/dx
EDGE: bpP:p9:good | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:sec-bnf#data@L122-L122 | NR_4 notation of Definition good
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: created from p11b:prose-L120-L124 (SPEC section data, tag p11b:prose-L120-L124); consumers: char, homological, flow, lie, lift-map, birkhoff-form and their steps

NODE: bpP:p11b:char
KIND: lemma
TITLE: Character decomposition
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:char@L126-L128
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:char@L129-L132
CONTRACT_ID: bpP:p11b:char
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: F a quartic family on O (sec-bnf#data) and k in Z^2; F_k(Lambda,z)=(2pi)^(-2) int_{[0,2pi]^2} e^{-i k.theta} F(Lambda,T_theta z) d theta
SOURCE_QUANTIFIERS: F; k in Z^2; Lambda in O, z, phi
SOURCE_CONCLUSION: F_k(Lambda,T_phi z)=e^{i k.phi} F_k(Lambda,z); F_k!=0 only if ¦k¦_1<=4; F=sum_k F_k (finite sum); F_k-bar=F_{-k} for real F; F_k is a polynomial in (z,z-bar) with real-analytic coefficients in Lambda and {F_k,N_0}=i(k.Omega)F_k; in particular <F>:=F_0 is the T^2-average of F and a real quartic family
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p11b:ch-mon, stepP:p11b:ch-bra, bpP:p11b:sec-bnf#data, bpP:p11b:sec-set#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p11b:ch-mon | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:char@L130-L130 | proof step: monomials and orthogonality
EDGE: stepP:p11b:ch-bra | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:char@L131-L131 | proof step: reality and bracket
EDGE: bpP:p11b:sec-bnf#data | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:char@L127-L127 | quartic family, N_0, T_theta
EDGE: bpP:p11b:sec-set#data | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:char@L126-L128 | The bracket in the conclusion uses the frozen slow-variable sign convention.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b+sol-review-P-m
REVIEWER: sol-delta-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p11b:ch-mon
KIND: step
TITLE: Monomials
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:ch-mon@L130-L130
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:ch-mon@L130-L130
CONTRACT_ID: stepP:p11b:ch-mon
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: quartic family written in z_j, z-bar_j as a combination of z^alpha zbar^beta with ¦alpha¦+¦beta¦=4; T_theta(z^alpha zbar^beta)=e^{i k.theta} z^alpha zbar^beta with k=beta-alpha
SOURCE_QUANTIFIERS: k in Z^2
SOURCE_CONCLUSION: ¦k¦_1<=4; orthogonality of characters gives F_k=sum_{beta-alpha=k} f_{alpha beta} z^alpha zbar^beta, F=sum F_k, covariance of F_k
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p11b:sec-bnf#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p11b:sec-bnf#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:ch-mon@L130-L130 | quartic family and the rotation action T_theta
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p11b:ch-bra
KIND: step
TITLE: Reality and bracket
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:ch-bra@L131-L131
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:ch-bra@L131-L131
CONTRACT_ID: stepP:p11b:ch-bra
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: covariance F_k(T_phi z)=e^{i k.phi}F_k(z); psi^t_{N_0}=T_{t Omega}
SOURCE_QUANTIFIERS: k in Z^2; F real
SOURCE_CONCLUSION: F_k-bar=F_{-k} for real F (conjugate the definition); {F_k,N_0}=d/dt F_k(T_{t Omega} z)¦_0=i(k.Omega)F_k
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p11b:ch-mon, bpP:p11b:sec-bnf#data, bpP:p11b:sec-set#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p11b:ch-mon | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:ch-bra@L131-L131 | covariance just proved
EDGE: bpP:p11b:sec-bnf#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:ch-bra@L131-L131 | N_0 and its flow T_{t Omega}
EDGE: bpP:p11b:sec-set#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:ch-bra@L131-L131 | bracket {F,G}=dF(X_G)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p11b:homological
KIND: lemma
TITLE: Homological equation
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:homological@L134-L138
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:homological@L139-L142
CONTRACT_ID: bpP:p11b:homological
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: F a quartic family on O; NR_4(Omega) on O (eq:nr)
SOURCE_QUANTIFIERS: F, O, Omega
SOURCE_CONCLUSION: chi:=sum_{k!=0} F_k/(i(k.Omega)) is a real quartic family (coefficients real analytic on O) and {chi,N_0}=F-<F>, equivalently {N_0,chi}=-(F-<F>)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p11b:ho-def, stepP:p11b:ho-eq, bpP:p11b:char, bpP:p11b:sec-bnf#data, bpP:p11b:sec-set#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p11b:ho-def | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:homological@L140-L140 | proof step: well defined and real
EDGE: stepP:p11b:ho-eq | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:homological@L141-L141 | proof step: the equation
EDGE: bpP:p11b:char | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:homological@L136-L136 | F_k and <F>
EDGE: bpP:p11b:sec-bnf#data | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:homological@L135-L135 | O, Omega, NR_4 and N_0
EDGE: bpP:p11b:sec-set#data | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:homological@L134-L138 | The two bracket identities use the section bracket and sign convention.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b+sol-review-P-m
REVIEWER: sol-delta-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p11b:ho-def
KIND: step
TITLE: Well defined, real
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:ho-def@L140-L140
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:ho-def@L140-L140
CONTRACT_ID: stepP:p11b:ho-def
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: finitely many k with 0<¦k¦_1<=4; k.Omega!=0 on O; F_k-bar=F_{-k}
SOURCE_QUANTIFIERS: Lambda in O
SOURCE_CONCLUSION: the sum defining chi is finite with k.Omega nonzero and analytic, and conj(F_k/(i k.Omega))=F_{-k}/(i(-k).Omega), so chi is real
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p11b:char, bpP:p11b:sec-bnf#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p11b:char | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:ho-def@L140-L140 | finite character decomposition and reality F_k-bar=F_{-k}
EDGE: bpP:p11b:sec-bnf#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:ho-def@L140-L140 | NR_4: k.Omega!=0 for 0<¦k¦_1<=4
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p11b:ho-eq
KIND: step
TITLE: Equation
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:ho-eq@L141-L141
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:ho-eq@L141-L141
CONTRACT_ID: stepP:p11b:ho-eq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Lemma char: {F_k,N_0}=i(k.Omega)F_k; antisymmetry of the bracket
SOURCE_QUANTIFIERS: Lambda in O
SOURCE_CONCLUSION: {chi,N_0}=sum_{k!=0} i(k.Omega)F_k/(i(k.Omega))=F-F_0; hence {N_0,chi}=-(F-<F>)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p11b:char, stepP:p11b:ho-def, bpP:p11b:sec-set#data, bpP:p11b:sec-bnf#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p11b:char | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:ho-eq@L141-L141 | {F_k,N_0}=i(k.Omega)F_k
EDGE: stepP:p11b:ho-def | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:ho-eq@L141-L141 | chi well defined
EDGE: bpP:p11b:sec-set#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:ho-eq@L141-L141 | Uses the bracket convention in computing the equation and its antisymmetric form.
EDGE: bpP:p11b:sec-bnf#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:ho-eq@L141-L141 | Uses N_0 and Omega in the displayed homological equation.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b+sol-review-P-m
REVIEWER: sol-delta-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p11b:flow
KIND: lemma
TITLE: Time-one map of a quartic Hamiltonian
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:flow@L144-L146
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:flow@L147-L150
CONTRACT_ID: bpP:p11b:flow
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: chi a quartic family on O; K subset O compact
SOURCE_QUANTIFIERS: chi, K; then C_1, r_1 (depending on chi and K); Lambda in K, ¦z¦_2<r_1
SOURCE_CONCLUSION: there are C_1, r_1>0 such that for Lambda in K and ¦z¦_2<r_1 the flow phi_chi^t of X_chi(Lambda,.) exists for t in [0,1], ¦phi_chi^t(z)¦_2^2<=2¦z¦_2^2, and Y(Lambda,z):=phi_chi^1(Lambda,z) is real analytic in (Lambda,z) on a neighbourhood of K x {¦z¦<r_1}, Y=z+O(¦z¦^3) uniformly, injective with inverse phi_{-chi}^1 on its image
CONSTANT_SCOPE: C_1, r_1 depend on chi and K (not on Lambda in K, z)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p11b:fl-bd, stepP:p11b:fl-an, bpP:p11b:sec-bnf#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p11b:fl-bd | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:flow@L148-L148 | proof step: bound and existence up to time one
EDGE: stepP:p11b:fl-an | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:flow@L149-L149 | proof step: analyticity and expansion
EDGE: bpP:p11b:sec-bnf#data | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:flow@L145-L145 | quartic family and O
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p11b:fl-bd
KIND: step
TITLE: Bound
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:fl-bd@L148-L148
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:fl-bd@L148-L148
CONTRACT_ID: stepP:p11b:fl-bd
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: X_chi polynomial vector field homogeneous of degree 3 in z with coefficients analytic in Lambda; K compact; u=¦z(t)¦^2
SOURCE_QUANTIFIERS: Lambda in K
SOURCE_CONCLUSION: ¦X_chi¦<=C_1¦z¦^3 on K; u-dot=2 z.X_chi<=2 C_1 u^2 so 1/u(t)>=1/u_0-2 C_1 t; for u_0<=r_1^2:=1/(4 C_1), u(t)<=2 u_0 on [0,1] and the solution cannot blow up
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: N:bpN:p3:gen-continuation, bpP:p11b:sec-bnf#data, bpP:p11b:sec-set#data
ROUTES: -
ROUTE_FOR: -
EDGE: N:bpN:p3:gen-continuation | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:fl-bd@L148-L148 | no blow-up: the solution stays in a compact set up to time one
EDGE: bpP:p11b:sec-bnf#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:fl-bd@L148-L148 | quartic family chi
EDGE: bpP:p11b:sec-set#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:fl-bd@L148-L148 | X_chi of the frozen sign convention
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b+sol-review-P-m
REVIEWER: sol-delta-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: L148 invokes N:bpN:p3:gen-continuation, which assumes an existing maximal solution of a C^1 field and a set with uniform data (delta,M,L). The polynomial field is C^1 and the displayed bound confines any existing trajectory, but no edge supplies the initial local/maximal solution or the uniform-data reduction on the confining ball. The differential inequality and its printed radius are retained; existence is not added as a source premise.

NODE: stepP:p11b:fl-an
KIND: step
TITLE: Analyticity, expansion
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:fl-an@L149-L149
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:fl-an@L149-L149
CONTRACT_ID: stepP:p11b:fl-an
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the flow of the real-analytic (polynomial) vector field X_chi exists up to time one with ¦phi^t¦^2<=2¦z¦^2
SOURCE_QUANTIFIERS: Lambda in K, ¦z¦<r_1
SOURCE_CONCLUSION: Y is real analytic in (Lambda,z); phi^1_chi(z)-z=int_0^1 X_chi(phi^t) dt=O(¦z¦^3); the inverse is the time-one map of -chi (uniqueness)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p11b:e-ode, N:bpN:p3:gen-uniqueness, stepP:p11b:fl-bd
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p11b:e-ode | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:fl-an@L149-L149 | analytic dependence of the flow on time, initial data and parameters
EDGE: N:bpN:p3:gen-uniqueness | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:fl-an@L149-L149 | inverse of phi^1_chi is phi^1_{-chi}
EDGE: stepP:p11b:fl-bd | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:fl-an@L149-L149 | existence on [0,1] and the bound ¦phi^t(z)¦^2<=2¦z¦^2 giving O(¦z¦^3)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p11b:lie
KIND: proposition
TITLE: Birkhoff normal form of order four
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:lie@L152-L159
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:lie@L160-L164
CONTRACT_ID: bpP:p11b:lie
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: O, Omega satisfying NR_4 (eq:nr); K(Lambda,z) real analytic on a neighbourhood of O x {0} with K=C+N_0+F+R, C=C(Lambda), F a quartic family, R analytic with vanishing 5-jet at z=0 (so R=O(¦z¦^6) locally uniformly); chi given by Lemma homological; Y=phi^1_chi
SOURCE_QUANTIFIERS: O, Omega, K, C, F, R; then for every compact K subset O: C_2, r_2; Lambda in K, ¦z¦<r_2
SOURCE_CONCLUSION: ¦K(Lambda,Y(Lambda,z))-(C(Lambda)+N_0(Lambda,z)+<F>(Lambda,z))¦<=C_2¦z¦^6, where <F> is the T^2-average, a quartic polynomial in R_1, R_2 only: <F>=sum_{i<=j} phi_ij(Lambda) R_i R_j
CONSTANT_SCOPE: C_2, r_2 depend on the compact set K (and on the data O, Omega, K, F, R)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p11b:li-tay, stepP:p11b:li-ord, stepP:p11b:li-sum, bpP:p8:e-taylor, bpP:p11b:homological, bpP:p11b:flow, bpP:p11b:char, bpP:p11b:sec-bnf#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p11b:li-tay | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:lie@L161-L161 | proof step: Taylor along the flow
EDGE: stepP:p11b:li-ord | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:lie@L162-L162 | proof step: orders
EDGE: stepP:p11b:li-sum | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:lie@L163-L163 | proof step: sum
EDGE: bpP:p8:e-taylor | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:lie@L155-L155 | R analytic with vanishing 5-jet is O(¦z¦^6) locally uniformly (alias of the Taylor external e-jet)
EDGE: bpP:p11b:homological | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:lie@L155-L155 | chi of Lemma homological
EDGE: bpP:p11b:flow | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:lie@L155-L155 | Y=phi^1_chi exists and is analytic on K x {¦z¦<r_1}
EDGE: bpP:p11b:char | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:lie@L157-L157 | <F> the T^2-average, a polynomial in R_1, R_2
EDGE: bpP:p11b:sec-bnf#data | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:lie@L153-L153 | O, Omega, N_0, quartic families
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p11b:li-tay
KIND: step
TITLE: Taylor along the flow
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:li-tay@L161-L161
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:li-tay@L161-L161
CONTRACT_ID: stepP:p11b:li-tay
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K analytic, t in [0,1], phi^t_chi the flow of chi
SOURCE_QUANTIFIERS: t in [0,1]
SOURCE_CONCLUSION: d/dt K o phi^t_chi={K,chi} o phi^t_chi, hence K o Y=K+{K,chi}+int_0^1(1-t){{K,chi},chi} o phi^t_chi dt
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: N:bpN:p5:lie-derivative, N:bpN:p5:taylor, bpP:p11b:flow, bpP:p11b:sec-set#data
ROUTES: -
ROUTE_FOR: -
EDGE: N:bpN:p5:lie-derivative | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:li-tay@L161-L161 | derivative of K along the flow is the Lie derivative
EDGE: N:bpN:p5:taylor | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:li-tay@L161-L161 | Taylor formula with integral remainder along the flow
EDGE: bpP:p11b:flow | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:li-tay@L161-L161 | flow phi^t_chi exists on [0,1] on the domain
EDGE: bpP:p11b:sec-set#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:li-tay@L161-L161 | bracket {K,chi}=dK(X_chi)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b+sol-review-P-m
REVIEWER: sol-delta-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: L161 cites N:bpN:p5:lie-derivative and N:bpN:p5:taylor. Those statements inherit a holomorphic Hamiltonian on a complex open domain, a complex norm with field bound epsilon<=1/2 and an initial point in Omega^{1/2}, with the trajectory in the domain of the holomorphic observable. Here K and the Lambda-dependent coefficients are stated real analytic and flow supplies a real time-one map. No complexification, compatible complex domain/norm or small-field verification is supplied. The real chain-rule/integral-Taylor formula is asserted in L161, but its direct real version has no supplying approved input either. The printed real statement is retained without adding those proof obligations as hypotheses.

NODE: stepP:p11b:li-ord
KIND: step
TITLE: Orders
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:li-ord@L162-L162
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:li-ord@L162-L162
CONTRACT_ID: stepP:p11b:li-ord
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: {N_0,chi}=-(F-<F>) (Lemma homological); degrees of F, chi, X_chi; ¦phi^t_chi z¦^2<=2¦z¦^2 (Lemma flow)
SOURCE_QUANTIFIERS: Lambda in K, ¦z¦ small
SOURCE_CONCLUSION: {K,chi}=-(F-<F>)+O(¦z¦^6) ({F,chi} has degree 6, {R,chi}=O(¦z¦^8), {C,chi}=0); {K,chi}=O(¦z¦^4) analytic so {{K,chi},chi}=O(¦z¦^6), and on phi^t_chi(z) it is <=C¦z¦^6
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p11b:homological, bpP:p8:e-taylor, bpP:p11b:flow, bpP:p11b:sec-set#data, bpP:p11b:sec-bnf#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p11b:homological | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:li-ord@L162-L162 | {N_0,chi}=-(F-<F>)
EDGE: bpP:p8:e-taylor | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:li-ord@L162-L162 | jet and O(¦z¦^k) estimates of analytic functions (alias of e-jet)
EDGE: bpP:p11b:flow | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:li-ord@L162-L162 | ¦phi^t_chi z¦^2<=2¦z¦^2 along the flow
EDGE: bpP:p11b:sec-set#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:li-ord@L162-L162 | Computes slow-variable brackets using the section convention.
EDGE: bpP:p11b:sec-bnf#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:li-ord@L162-L162 | Uses N_0 and the quartic-family degrees in the bracket order calculation.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b+sol-review-P-m
REVIEWER: sol-delta-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p11b:li-sum
KIND: step
TITLE: Sum
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:li-sum@L163-L163
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:li-sum@L163-L163
CONTRACT_ID: stepP:p11b:li-sum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K o Y=K+{K,chi}+int...; {K,chi}=-(F-<F>)+O(¦z¦^6); {{K,chi},chi} o phi^t=O(¦z¦^6)
SOURCE_QUANTIFIERS: Lambda in K, ¦z¦<r_2
SOURCE_CONCLUSION: K o Y=C+N_0+F+R-(F-<F>)+O(¦z¦^6)=C+N_0+<F>+O(¦z¦^6); <F> is T_theta-invariant hence a polynomial in ¦z_1¦^2, ¦z_2¦^2 of degree 2 in (R_1,R_2)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p11b:li-tay, stepP:p11b:li-ord, bpP:p11b:char, bpP:p11b:sec-bnf#data, bpP:p11b:sec-set#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p11b:li-tay | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:li-sum@L163-L163 | the formula for K o Y
EDGE: stepP:p11b:li-ord | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:li-sum@L163-L163 | the order bounds
EDGE: bpP:p11b:char | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:li-sum@L163-L163 | <F> is the T^2-average, T-invariant
EDGE: bpP:p11b:sec-bnf#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:li-sum@L163-L163 | Uses T_theta invariance and R_1,R_2 in identifying the averaged polynomial.
EDGE: bpP:p11b:sec-set#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:li-sum@L163-L163 | R_j=(x_j^2+y_j^2)/2 is defined in the section setting; L163 identifies the averaged quartic as a degree-two polynomial in R_1,R_2.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b+sol-delta-P-m
REVIEWER: sol-delta2-P-t
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p11b:lift-map
KIND: proposition
TITLE: The Birkhoff map on the full phase space
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:lift-map@L166-L172
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:lift-map@L173-L176
CONTRACT_ID: bpP:p11b:lift-map
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the situation of Lemma flow; O prime open with closure compact in O (O prime ⋐ O); r_1=r_1(closure of O prime) the radius of Lemma flow; Phi_chi(lambda,Lambda,z)=(lambda+g(Lambda,z),Lambda,Y(Lambda,z)) on R^2 x O prime x {¦z¦_2<r_1} with g_l(Lambda,z)=int_0^1 d_{Lambda_l} chi(Lambda,phi^t_chi(Lambda,z)) dt; the chart form Omega_chart=dLambda^dlambda+dy^dx; the lift Phi_rho of Proposition bpP:p9:lift (defined on all of R^2 x O)
SOURCE_QUANTIFIERS: chi, O, O prime (relatively compact in O), r_1; rho; points (lambda,Lambda,z) of the domain
SOURCE_CONCLUSION: Phi_chi is the time-one map of the Hamiltonian flow of chi for Omega_chart; hence a real analytic symplectic diffeomorphism of R^2 x O prime x {¦z¦_2<r_1} onto its image, preserving Lambda and commuting with angle translations Phi_chi(lambda+c,Lambda,z)=Phi_chi(lambda,Lambda,z)+(c,0,0); T:=Phi_rho^(-1) o Phi_chi has the same three properties on the same domain and T(lambda,Lambda,z)=(lambda+g(Lambda,z)+H(Lambda,Y(Lambda,z)), Lambda, rho(Lambda) Y(Lambda,z)) with H_l(Lambda,z-tilde)=y-tilde^T(rho^T d_{Lambda_l} rho)x-tilde
CONSTANT_SCOPE: r_1 depends on O prime and chi (uniform only on compact sets, hence O prime relatively compact)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p11b:lm-ham, stepP:p11b:lm-prop, bpP:p11b:flow, bpP:p9:lift, bpP:p11b:sec-bnf#data, bpP:p11b:sec-set#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p11b:lm-ham | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:lift-map@L174-L174 | proof step: Hamilton equations
EDGE: stepP:p11b:lm-prop | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:lift-map@L175-L175 | proof step: properties
EDGE: bpP:p11b:flow | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:lift-map@L167-L167 | phi^t_chi, Y and r_1 of Lemma flow
EDGE: bpP:p9:lift | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:lift-map@L169-L169 | the lift Phi_rho and its properties
EDGE: bpP:p11b:sec-bnf#data | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:lift-map@L167-L167 | quartic family chi, O, Omega
EDGE: bpP:p11b:sec-set#data | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:lift-map@L167-L167 | chart form dLambda^dlambda+dy^dx, rho, R_j
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p11b:lm-ham
KIND: step
TITLE: Hamilton's equations
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:lm-ham@L174-L174
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:lm-ham@L174-L174
CONTRACT_ID: stepP:p11b:lm-ham
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: chi does not depend on lambda; Hamiltonian of chi for the chart form; Y=phi^1_chi
SOURCE_QUANTIFIERS: (lambda,Lambda,z) in the domain
SOURCE_CONCLUSION: Lambda-dot=-d_lambda chi=0, z-dot=X_chi(Lambda,z), lambda-dot_l=d_{Lambda_l} chi(Lambda,z(t)); integrating, lambda(1)=lambda+g and z(1)=Y
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p11b:flow, bpP:p11b:sec-set#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p11b:flow | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:lm-ham@L174-L174 | Y=phi^1_chi
EDGE: bpP:p11b:sec-set#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:lm-ham@L174-L174 | chart form and sign convention for the Hamilton equations
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p11b:lm-prop
KIND: step
TITLE: Properties
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:lm-prop@L175-L175
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:lm-prop@L175-L175
CONTRACT_ID: stepP:p11b:lm-prop
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Lemma flow on K=closure of O prime; Hamiltonian flows are symplectic; Phi_chi from the previous step; Proposition lift for Phi_rho
SOURCE_QUANTIFIERS: (lambda,Lambda,z) in the domain
SOURCE_CONCLUSION: the flow exists up to time one for every point of the domain (uses O prime ⋐ O); Phi_chi is symplectic and analytic, preserves Lambda and commutes with lambda-translations; T=Phi_rho^(-1) o Phi_chi, a composition of two maps with these properties
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p11b:flow, bpP:p11b:e-ode, bpP:p9:lift, N:bpN:p5:symplectic, N:bpN:p5:canonical, stepP:p11b:lm-ham
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p11b:flow | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:lm-prop@L175-L175 | existence of the flow up to time one on the compact closure of O prime
EDGE: bpP:p11b:e-ode | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:lm-prop@L175-L175 | analyticity of the flow
EDGE: bpP:p9:lift | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:lm-prop@L175-L175 | Phi_rho has the same properties
EDGE: N:bpN:p5:symplectic | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:lm-prop@L175-L175 | Hamiltonian flows are symplectic
EDGE: N:bpN:p5:canonical | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:lm-prop@L175-L175 | canonical transformation property
EDGE: stepP:p11b:lm-ham | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:lm-prop@L175-L175 | Phi_chi is the time-one map of the Hamiltonian flow
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b+sol-review-P-m
REVIEWER: sol-delta-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: L175 invokes N:bpN:p5:symplectic and N:bpN:p5:canonical for the full (lambda,Lambda,z) Hamiltonian flow. These imports inherit N:bpN:p5:flow: a holomorphic field on a complex open domain, a chosen complex norm with field bound epsilon<=1/2, and initial points in Omega^{1/2}. The real compact-parameter flow of flow/fl-bd does not state these complex hypotheses; the full field also contains partial_Lambda chi in the angle components. No complexification/domain/smallness bridge or separately approved general real symplectic-flow theorem is supplied here. The asserted symplectic conclusion is retained, with this applicability gap explicit.

NODE: bpP:p11b:sec-beta#data
KIND: definition
TITLE: The spectral projection Pi_1 of Q_h (n=2)
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:sec-beta#data@L180-L182
PROOF_SOURCE: -
CONTRACT_ID: bpP:p11b:sec-beta#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a in A_2; sigma_1<sigma_2<0 the eigenvalues of Q_h(a) (Corollary bpP:p9:n2)
SOURCE_QUANTIFIERS: a in A_2
SOURCE_CONCLUSION: defines Pi_1(a)=(Q_h(a)-sigma_2 I)/(sigma_1-sigma_2)=[[pi_11,pi_12],[pi_12,pi_22]], the orthogonal projection onto the sigma_1-eigenspace (rank one: pi_11+pi_22=1, pi_11 pi_22=pi_12^2); with rho=[e_1¦e_2] in SO(2), Pi_1=e_1 e_1^T
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p11b:sec-set#data, bpP:p9:n2
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p11b:sec-set#data | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:sec-beta#data@L180-L180 | a in A_2 and Q_h(a)
EDGE: bpP:p9:n2 | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:sec-beta#data@L180-L180 | the eigenvalues sigma_1<sigma_2<0 of Q_h(a)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: created from p11b:prose-L180-L182 (SPEC section data); consumers: beta-def, beta-formula, bf-gram, bt-rot, as-pi

NODE: bpP:p11b:beta-def
KIND: definition
TITLE: Torsion $\hat\beta$
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:beta-def@L184-L192
PROOF_SOURCE: -
CONTRACT_ID: bpP:p11b:beta-def
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: c_1..c_6 of Theorem bpP:p11b:quartic-explicit; pi_ij the entries of Pi_1 (sec-beta#data); delta_pi=pi_11-pi_22
SOURCE_QUANTIFIERS: a in A_2
SOURCE_CONCLUSION: defines a=c_1 pi_11^2+c_2 pi_22^2+(c_3+c_4)pi_11 pi_22+(c_5 pi_11+c_6 pi_22)pi_12, d=c_1 pi_22^2+c_2 pi_11^2+(c_3+c_4)pi_11 pi_22-(c_5 pi_22+c_6 pi_11)pi_12, b=4(c_1+c_2)pi_11 pi_22+c_3 delta_pi^2+c_4(delta_pi^2/2-2 pi_11 pi_22)+2(c_6-c_5)pi_12 delta_pi and the symmetric matrix beta-hat(a)=[[8a,4b],[4b,8d]]; all entries real analytic on A_2, independent of the choice of rho (only Pi_1 enters), of the coupling parameter, and the same for S_fix and S_mov
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p11b:quartic-explicit, bpP:p11b:sec-beta#data, bpP:p9:n2, bpP:p8:same-jets
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p11b:quartic-explicit | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:beta-def@L185-L185 | c_1..c_6
EDGE: bpP:p11b:sec-beta#data | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:beta-def@L185-L185 | pi_ij, Pi_1
EDGE: bpP:p9:n2 | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:beta-def@L191-L191 | sigma_1,2=(tr -/+ sqrt(tr^2-4 det))/2 with positive discriminant: analyticity
EDGE: bpP:p8:same-jets | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:beta-def@L191-L191 | same beta-hat for S_fix and S_mov
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p11b:beta-formula
KIND: proposition
TITLE: $\hat\beta$ is the torus average of the rotated quartic
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:beta-formula@L194-L197
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:beta-formula@L198-L203
CONTRACT_ID: bpP:p11b:beta-formula
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: rho=[e_1¦e_2] in SO(2) diagonalising Q_h(a); Q_4-tilde(z)=Q_4(rho x,rho y), i.e. u_i=sum_j rho_ij z_j in Q_4 (Theorem quartic-explicit); T^2-average of Lemma char
SOURCE_QUANTIFIERS: a in A_2; rho; z
SOURCE_CONCLUSION: <Q_4-tilde>=(1/2) sum_{i,j} beta-hat_ij(a) R_i R_j=4a R_1^2+4b R_1 R_2+4d R_2^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p11b:bf-gram, stepP:p11b:bf-avg, bpP:p11b:quartic-explicit, bpP:p11b:char, bpP:p11b:beta-def, bpP:p11b:sec-beta#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p11b:bf-gram | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:beta-formula@L199-L199 | proof step: Gram variables
EDGE: stepP:p11b:bf-avg | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:beta-formula@L202-L202 | proof step: averaging
EDGE: bpP:p11b:quartic-explicit | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:beta-formula@L195-L195 | Q_4 and c_nu
EDGE: bpP:p11b:char | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:beta-formula@L195-L195 | the T^2-average <.>
EDGE: bpP:p11b:beta-def | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:beta-formula@L196-L196 | beta-hat_ij and a, b, d
EDGE: bpP:p11b:sec-beta#data | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:beta-formula@L195-L195 | Pi_1=e_1 e_1^T for the diagonalising rho
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p11b:bf-gram
KIND: step
TITLE: Gram variables
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bf-gram@L199-L201
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bf-gram@L199-L201
CONTRACT_ID: stepP:p11b:bf-gram
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: rho=[[gamma,-s],[s,gamma]]; e_1=(gamma,s); pi_11=gamma^2, pi_22=s^2, pi_12=gamma s; r_j=¦z_j¦^2=2R_j, g=z_1.z_2
SOURCE_QUANTIFIERS: a in A_2; z
SOURCE_CONCLUSION: u_1=gamma z_1-s z_2, u_2=s z_1+gamma z_2, A_1=¦u_1¦^2=pi_11 r_1+pi_22 r_2-2 pi_12 g, A_2=¦u_2¦^2=pi_22 r_1+pi_11 r_2+2 pi_12 g, B=u_1.u_2=pi_12(r_1-r_2)+delta_pi g, and Q_4-tilde=c_1 A_1^2+c_2 A_2^2+c_3 A_1 A_2+c_4 B^2+c_5 A_1 B+c_6 A_2 B is a polynomial in (r_1,r_2,g) of degree <=2 in g
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p11b:sec-beta#data, bpP:p11b:quartic-explicit, bpP:p11b:sec-set#data, bpP:p11b:beta-def
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p11b:sec-beta#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bf-gram@L199-L199 | pi_11, pi_22, pi_12 and their relations
EDGE: bpP:p11b:quartic-explicit | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bf-gram@L201-L201 | Q_4 in terms of c_nu
EDGE: bpP:p11b:sec-set#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bf-gram@L199-L201 | Uses R_j=(x_j^2+y_j^2)/2 and the slow-variable convention.
EDGE: bpP:p11b:beta-def | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bf-gram@L199-L201 | Uses delta_pi := pi_11-pi_22 in B_dot explicitly.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b+sol-review-P-m
REVIEWER: sol-delta-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p11b:bf-avg
KIND: step
TITLE: Averaging
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bf-avg@L202-L202
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bf-avg@L202-L202
CONTRACT_ID: stepP:p11b:bf-avg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Gram variables; T_theta: r_j invariant, g=Re(z_1-bar z_2) -> Re(e^{i(theta_1-theta_2)} z_1-bar z_2)
SOURCE_QUANTIFIERS: a in A_2
SOURCE_CONCLUSION: <g>=0, <g^2>=r_1 r_2/2; collecting coefficients of r_1^2, r_2^2 and r_1 r_2 (+g^2/2) with pi_11 pi_22=pi_12^2, pi_11+pi_22=1 gives a, d, b; hence <Q_4-tilde>=a r_1^2+b r_1 r_2+d r_2^2=4a R_1^2+4b R_1 R_2+4d R_2^2=(1/2) sum beta-hat_ij R_i R_j
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p11b:bf-gram, bpP:p11b:beta-def, bpP:p11b:sec-bnf#data, bpP:p11b:sec-beta#data, bpP:p11b:e-ca
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p11b:bf-gram | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bf-avg@L202-L202 | the polynomial in (r_1,r_2,g)
EDGE: bpP:p11b:beta-def | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bf-avg@L202-L202 | coefficients a, b, d and beta-hat
EDGE: bpP:p11b:sec-bnf#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bf-avg@L202-L202 | rotation action T_theta
EDGE: bpP:p11b:sec-beta#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bf-avg@L202-L202 | pi_11 pi_22=pi_12^2, pi_11+pi_22=1
EDGE: bpP:p11b:e-ca | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bf-avg@L202-L202 | the remaining coefficient bookkeeping is verified symbolically
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p11b:birkhoff-form
KIND: theorem
TITLE: Secular Birkhoff form, planar
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:birkhoff-form@L205-L215
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:birkhoff-form@L216-L222
CONTRACT_ID: bpP:p11b:birkhoff-form
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n=2; G, m0>0; m_1, m_2>0; K_a=closed B_inf(a^0,rho) subset {a in A_2: Phi_4(a)!=0} a closed cube; O_a open with K_a subset O_a subset {Phi_4!=0}, simply connected; Lambda(.) the analytic diffeomorphism a->Lambda; K=Lambda(K_a), O=Lambda(O_a)
SOURCE_QUANTIFIERS: n=2, G, m0, m_1, m_2; then K_a, O_a; then rho (rotation), chi, O prime, r_*, C_*, T; then in (b) Lambda in K, ¦z¦_2<r_*; in (c) V, mu_0, r_0
SOURCE_CONCLUSION: there are an analytic rho: O -> SO(2) diagonalising Q_h, analytic chi (Lemma homological with F=Q_4-tilde, Omega=2 sigma), an open O prime with K subset O prime ⋐ O, constants r_*>0, C_*>0 and the analytic symplectic map T=Phi_rho^(-1) o Phi_chi on T-domain={(lambda,Lambda,z): Lambda in O prime, ¦z¦_2<r_*}, with r_*<=rho_K/sqrt2 and r_*<=min{r_1(closure O prime), r_2}, such that T takes values in the domain of analyticity of f-hat_mov (and f-hat_fix) and, for f-hat in {f_fix, f_mov} and P:=f-hat o T: (a) P real analytic on the domain, 2pi-periodic in lambda, independent of any coupling parameter, H^Psi o T=h(Lambda)+mu P for H^Psi=h+mu f-hat; (b) for Lambda in K, ¦z¦_2<r_*: <P>=P_0(Lambda)+sum_j Omega_j R_j+(1/2) sum beta-hat_ij(a(Lambda)) R_i R_j+Rem, ¦Rem¦<=C_*¦z¦^6, with Omega_j=2 sigma_j(a(Lambda))<0, P_0=C_0(a) (fix) or C_0(a)+delta(Lambda) (mov); (c) with (I,phi,p,q)=(Lambda,lambda,y,x), the frozen HasBirkhoff(P,V,r_0,mu_0,P_0,Omega,beta) of Definition p0:birkhoff holds for V=int K, any mu_0>0, every r_0 in (0,r_*/sqrt2], Omega(mu,I)=2 sigma(a(I)), beta(mu,I)=beta-hat(a(I)) (symmetric), P_0 as above, all independent of mu, P extended as in Part 12
CONSTANT_SCOPE: rho, chi, r_*, C_* depend only on (G, m0, m, K_a)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p11b:bt-rot, stepP:p11b:bt-K, stepP:p11b:bt-nf, stepP:p11b:bt-avg, stepP:p11b:bt-frozen, bpP:p11b:homological, bpP:p11b:lift-map, bpP:p11b:flow, bpP:p11b:lie, bpP:p8:perturbation-analytic, bpP:p8:identification, bpP:p11b:beta-def, bpP:p9:good, bpP:p0:birkhoff#HasSecularBirkhoffForm, bpP:p11b:sec-set#data, bpP:p11b:sec-bnf#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p11b:bt-rot | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:birkhoff-form@L217-L217 | proof step: rotation
EDGE: stepP:p11b:bt-K | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:birkhoff-form@L218-L218 | proof step: the function K
EDGE: stepP:p11b:bt-nf | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:birkhoff-form@L219-L219 | proof step: normal form
EDGE: stepP:p11b:bt-avg | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:birkhoff-form@L220-L220 | proof step: average of P
EDGE: stepP:p11b:bt-frozen | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:birkhoff-form@L221-L221 | proof step: the frozen clauses
EDGE: bpP:p11b:homological | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:birkhoff-form@L206-L206 | chi of Lemma homological with F=Q_4-tilde, Omega=2 sigma
EDGE: bpP:p11b:lift-map | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:birkhoff-form@L206-L206 | T=Phi_rho^(-1) o Phi_chi
EDGE: bpP:p11b:flow | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:birkhoff-form@L206-L206 | r_1(closure O prime)
EDGE: bpP:p11b:lie | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:birkhoff-form@L206-L206 | r_2
EDGE: bpP:p8:perturbation-analytic | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:birkhoff-form@L206-L206 | polydisc domain of analyticity of f-hat
EDGE: bpP:p8:identification | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:birkhoff-form@L211-L211 | delta(Lambda) in P_0 for f-hat_mov
EDGE: bpP:p11b:beta-def | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:birkhoff-form@L210-L210 | beta-hat in (b) and (c)
EDGE: bpP:p9:good | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:birkhoff-form@L206-L206 | Phi_4, the set {Phi_4!=0}
EDGE: bpP:p0:birkhoff#HasSecularBirkhoffForm | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:birkhoff-form@L212-L212 | the frozen HasBirkhoff clauses of (c)
EDGE: bpP:p11b:sec-set#data | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:birkhoff-form@L206-L206 | A_2, Lambda(.), chart, Q_h, rho, sigma
EDGE: bpP:p11b:sec-bnf#data | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:birkhoff-form@L205-L215 | Uses the quartic family, N_0 and the homological setting with Omega=2 sigma.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b+sol-review-P-m
REVIEWER: sol-delta-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p11b:bt-rot
KIND: step
TITLE: Rotation
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-rot@L217-L217
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-rot@L217-L217
CONTRACT_ID: stepP:p11b:bt-rot
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Q_h has simple spectrum on O_a (O_a subset {Phi_4!=0}); Pi_1 analytic there; O_a simply connected
SOURCE_QUANTIFIERS: a in O_a
SOURCE_CONCLUSION: e_1 (a unit vector in the range of Pi_1) lifts analytically to an angle psi on the simply connected O_a (covering S^1->S^1); put rho=[e_1¦e_2], e_2=J e_1, analytic with values in SO(2) diagonalising Q_h
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p9:local-analytic, bpP:p9:diagonalize, bpP:p11b:sec-beta#data, bpP:p9:good-set, stepP:p11b:bt-rot#lift
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p9:local-analytic | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-rot@L217-L217 | analytic simple eigenvalues and rotation locally
EDGE: bpP:p9:diagonalize | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-rot@L217-L217 | Theorem diagonalize(a)
EDGE: bpP:p11b:sec-beta#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-rot@L217-L217 | Pi_1 analytic
EDGE: bpP:p9:good-set | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-rot@L217-L217 | Phi_4!=0 implies simple spectrum on O_a (part (b))
EDGE: stepP:p11b:bt-rot#lift | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-rot@L217-L217 | lift of e_1 to an analytic angle on the simply connected O_a
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: the lifting step (analytic angle on a simply connected domain) is recorded as stepP:p11b:bt-rot#lift (SOURCE_GAP)

NODE: stepP:p11b:bt-rot#lift
KIND: step
TITLE: Lift of the eigenvector e_1 to an analytic angle on a simply connected domain
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-rot#lift@L217-L217
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-rot#lift@L217-L217
CONTRACT_ID: stepP:p11b:bt-rot#lift
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: O_a open and simply connected; e_1: O_a -> S^1 real analytic (a unit vector in the range of the analytic projection Pi_1, defined up to sign)
SOURCE_QUANTIFIERS: O_a, e_1
SOURCE_CONCLUSION: there is a real analytic angle psi: O_a -> R with e_1=(cos psi, sin psi) (covering S^1->S^1), so that rho=[e_1¦e_2] is analytic into SO(2)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p9:local-analytic, bpP:p11b:sec-beta#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p9:local-analytic | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-rot#lift@L217-L217 | local analytic eigenvector data to be lifted
EDGE: bpP:p11b:sec-beta#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-rot#lift@L217-L217 | Pi_1 analytic, e_1 in its range
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: the covering-space lifting of an analytic unit vector field (defined only up to sign locally) to an analytic angle on a simply connected domain is asserted in one parenthesis; it is neither proved in the corpus nor a listed external (e-ode, e-id, e-jet, e-ca). Corollary bpP:p9:n2 states a global analytic rotation on all of A_2, which would supply rho on O_a, but this proof does not cite it. For the cube used by Part 12 (Corollary patch) the domain is convex

NODE: stepP:p11b:bt-K
KIND: step
TITLE: The function $K$
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-K@L218-L218
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-K@L218-L218
CONTRACT_ID: stepP:p11b:bt-K
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: S_fix=C_0+xi^T Q_h xi+eta^T Q_h eta+Q_4+R_6 with R_6 analytic with vanishing 5-jet; K(Lambda,z)=S_fix(Lambda,rho x,rho y); the polydisc domain of Proposition perturbation-analytic
SOURCE_QUANTIFIERS: Lambda in K
SOURCE_CONCLUSION: K=C_0+N_0+Q_4-tilde+R with Omega=2 sigma and R=R_6 o (rho .); K is analytic on a neighbourhood of K x {0}; rho_K is chosen by compactness (finite cover by N(rho_*(Lambda^*)/2)) so that real polydiscs of radius rho_K around (0,Lambda_c,0), Lambda_c in K, lie in the domain of Proposition perturbation-analytic
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p8:quadratic-form, bpP:p8:evenness, bpP:p11b:quartic-explicit, bpP:p9:diagonalize, bpP:p8:perturbation-analytic, stepP:p11b:bt-rot, bpP:p11b:sec-bnf#data, bpP:p11b:sec-set#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p8:quadratic-form | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-K@L218-L218 | S_fix=C_0+quadratic part+O(4)
EDGE: bpP:p8:evenness | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-K@L218-L218 | only even degrees: the remainder after degree four has vanishing 5-jet
EDGE: bpP:p11b:quartic-explicit | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-K@L218-L218 | degree-four part Q_4
EDGE: bpP:p9:diagonalize | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-K@L218-L218 | diagonal form of the quadratic part in rho-rotated variables with Omega=2 sigma
EDGE: bpP:p8:perturbation-analytic | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-K@L218-L218 | polydisc domain and rho_*
EDGE: stepP:p11b:bt-rot | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-K@L218-L218 | rho
EDGE: bpP:p11b:sec-bnf#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-K@L218-L218 | N_0 with Omega=2 sigma
EDGE: bpP:p11b:sec-set#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-K@L218-L218 | S_fix, C_0, Q_h
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p11b:bt-nf
KIND: step
TITLE: Normal form
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-nf@L219-L219
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-nf@L219-L219
CONTRACT_ID: stepP:p11b:bt-nf
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: F=Q_4-tilde is a quartic family (coefficients analytic in Lambda through c_nu and rho); Phi_4!=0 on O; K=C_0+N_0+Q_4-tilde+R
SOURCE_QUANTIFIERS: Lambda in K
SOURCE_CONCLUSION: NR_4(Omega) holds on O since Phi_4!=0 (NR_4(sigma) iff NR_4(2 sigma)); Proposition lie gives K o Y=C_0+N_0+<Q_4-tilde>+O(¦z¦^6), and <Q_4-tilde>=(1/2) sum beta-hat_ij R_i R_j
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p9:good-set, bpP:p11b:lie, bpP:p11b:beta-formula, stepP:p11b:bt-K, bpP:p11b:quartic-explicit, stepP:p11b:bt-rot, bpP:p11b:sec-bnf#data, bpP:p11b:beta-def, bpP:p11b:sec-set#data, bpP:p9:good
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p9:good-set | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-nf@L219-L219 | Phi_4!=0 iff NR_4(sigma) (part (b))
EDGE: bpP:p11b:lie | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-nf@L219-L219 | K o Y=C_0+N_0+<Q_4-tilde>+O(¦z¦^6)
EDGE: bpP:p11b:beta-formula | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-nf@L219-L219 | <Q_4-tilde>=(1/2) sum beta-hat_ij R_i R_j
EDGE: stepP:p11b:bt-K | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-nf@L219-L219 | K=C_0+N_0+Q_4-tilde+R
EDGE: bpP:p11b:quartic-explicit | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-nf@L219-L219 | coefficients c_nu analytic
EDGE: stepP:p11b:bt-rot | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-nf@L219-L219 | rho analytic
EDGE: bpP:p11b:sec-bnf#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-nf@L219-L219 | NR_4(Omega), quartic family
EDGE: bpP:p11b:beta-def | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-nf@L219-L219 | Uses beta-hat_ij in the normal-form polynomial explicitly.
EDGE: bpP:p11b:sec-set#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-nf@L219-L219 | The physical Phi_4, ordered secular eigenvalues sigma, and frequency convention Omega=2 sigma are the fixed section data used in this application.
EDGE: bpP:p9:good | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-nf@L219-L219 | Definition good supplies Phi_4 and explicitly states NR_4(sigma) iff NR_4(2 sigma), used to verify the homological/normal-form premise.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b+sol-delta-P-m
REVIEWER: sol-delta2-P-t
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p11b:bt-avg
KIND: step
TITLE: Average of $P$
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-avg@L220-L220
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-avg@L220-L220
CONTRACT_ID: stepP:p11b:bt-avg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: T(lambda,Lambda,z)=(lambda+h_T(Lambda,z),Lambda,rho Y) with h_T independent of lambda; f-hat continuous and 2pi-periodic in lambda; Lambda in O prime, ¦z¦_2<r_*<=r_1; ¦rho Y¦<=¦Y¦<=sqrt2 ¦z¦ and r_*<=rho_K/sqrt2
SOURCE_QUANTIFIERS: Lambda in K, ¦z¦_2<r_*
SOURCE_CONCLUSION: the lambda-average of f-hat o T equals the average of f-hat at (Lambda,rho x-prime,rho y-prime), z-prime=Y(Lambda,z), i.e. S(Lambda,rho x-prime,rho y-prime)=K(Lambda,Y)+[delta]; T takes values in the polydisc domain for r_*<=rho_K/sqrt2, which gives (a); the remainder bound is Proposition lie (K=compact, ¦z¦<r_*<=r_2) with the identification [delta] of Theorem identification, giving (b)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p11b:lift-map, bpP:p8:perturbation-analytic, bpP:p8:e-diff, bpP:p11b:lie, bpP:p8:identification, bpP:p11b:flow, stepP:p11b:bt-K, stepP:p11b:bt-nf, stepP:p11b:bt-rot, bpP:p11b:sec-set#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p11b:lift-map | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-avg@L220-L220 | T=(lambda+h_T,Lambda,rho Y), lambda-independent shift
EDGE: bpP:p8:perturbation-analytic | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-avg@L220-L220 | f-hat continuous, 2pi-periodic in lambda, analytic polydisc domain
EDGE: bpP:p8:e-diff | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-avg@L220-L220 | translation invariance of the integral of a periodic continuous function
EDGE: bpP:p11b:lie | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-avg@L220-L220 | remainder bound C_*¦z¦^6 with r_*<=r_2
EDGE: bpP:p8:identification | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-avg@L220-L220 | S_mov=S_fix+delta(Lambda)
EDGE: bpP:p11b:flow | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-avg@L220-L220 | r_*<=r_1 and ¦Y¦<=sqrt2¦z¦
EDGE: stepP:p11b:bt-K | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-avg@L220-L220 | rho_K and the polydisc
EDGE: stepP:p11b:bt-nf | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-avg@L220-L220 | K o Y=C_0+N_0+<Q_4-tilde>+O(¦z¦^6)
EDGE: stepP:p11b:bt-rot | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-avg@L220-L220 | rho
EDGE: bpP:p11b:sec-set#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-avg@L220-L220 | S_fix, S_mov and the average
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p11b:bt-frozen
KIND: step
TITLE: The frozen clauses
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-frozen@L221-L221
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-frozen@L221-L221
CONTRACT_ID: stepP:p11b:bt-frozen
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Definition bpP:p0:birkhoff has two clauses (integrability and the epsilon-delta estimate) quantified over mu in [0,mu_0], I in V; 0<r_0<=r_*/sqrt2; oscillator discs p_j^2+q_j^2<r_0^2; P, <P>, Rem, beta-hat, Omega, P_0 independent of mu
SOURCE_QUANTIFIERS: mu in [0,mu_0], I in V; r_0; epsilon>0, delta<=r_0
SOURCE_CONCLUSION: the antecedent discs give ¦z¦_2^2<2 r_0^2<=r_*^2 so the point lies in the T-domain; (i) P is continuous on it, hence integrable over the torus, and the frozen secularAverage is <P>; (ii) for delta^2<=epsilon/(64 C_*) and ¦z¦_2<=2¦(p,q)¦_inf: ¦Rem¦<=C_*¦z¦^6<=64 C_*¦(p,q)¦_inf^6<=epsilon ¦(p,q)¦_inf^4 uniformly in I in K; both clauses hold for all mu in [0,mu_0]; symmetry of beta-hat supplies the symmetry hypothesis of P-G (it is not a clause of HasBirkhoff)
CONSTANT_SCOPE: delta depends on epsilon and C_*
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p0:birkhoff#HasSecularBirkhoffForm, bpP:p0:secavg#secularAverage, stepP:p11b:bt-avg, bpP:p11b:beta-def, bpP:p8:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:birkhoff#HasSecularBirkhoffForm | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-frozen@L221-L221 | the two clauses and their quantification
EDGE: bpP:p0:secavg#secularAverage | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-frozen@L221-L221 | frozen secularAverage is <P>
EDGE: stepP:p11b:bt-avg | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-frozen@L221-L221 | P analytic, T-domain, expansion of <P> with ¦Rem¦<=C_*¦z¦^6
EDGE: bpP:p11b:beta-def | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-frozen@L221-L221 | symmetry of beta-hat
EDGE: bpP:p8:conv#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:bt-frozen@L221-L221 | dictionary to the frozen secularAverage (section conv)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p11b:remain
KIND: claim
TITLE: Two clauses of P-G that remain for Part 12
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:remain@L224-L226
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:remain@L224-L226
CONTRACT_ID: bpP:p11b:remain
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Corollary bpP:p11b:patch; the setting of P-G (htorsion asks B<=¦det beta¦ on V)
SOURCE_QUANTIFIERS: the patch K_a (from Corollary patch)
SOURCE_CONCLUSION: (1) B:=min over K_a of ¦det beta-hat¦>0 satisfies htorsion (det beta-hat is continuous and nonzero on the compact K_a); (2) the joint analyticity of P near the closure of the cylinder, extension of P outside the T-domain, hperiod, the fast diffeomorphism and the boundary collar are Part 12 tasks; for n=2 and P-FIXED the same P_0, Omega, beta-hat (up to delta) serve
CONSTANT_SCOPE: B depends on the patch K_a
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p11b:patch, bpP:p11b:beta-def, bpP:p8:same-jets
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p11b:patch | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:remain@L225-L225 | det beta-hat continuous and nonzero on the compact K_a
EDGE: bpP:p11b:beta-def | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:remain@L225-L225 | beta-hat
EDGE: bpP:p8:same-jets | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:remain@L225-L225 | same P_0, Omega, beta-hat (up to delta) for S_fix and S_mov
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: consumed by Part 12 (stepP:p12:pg-h56 cites Remark remain(1)); clause (2) is a list of Part-12 tasks (pointer), its P-FIXED sentence is not used by P-PLANAR

NODE: bpP:p11b:asymptotics
KIND: proposition
TITLE: Hierarchical asymptotics of $\hat\beta$
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:asymptotics@L230-L238
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:asymptotics@L239-L248
CONTRACT_ID: bpP:p11b:asymptotics
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: G, m0, m_1, m_2>0, g_0:=G/kappa=1/m_0; a_2=1, a_1=alpha in (0,alpha_0) with alpha_0 depending only on m_1/m_2
SOURCE_QUANTIFIERS: G, m0, m_1, m_2; then alpha_0; then alpha in (0,alpha_0); the O(.) constants
SOURCE_CONCLUSION: beta-hat_11=(3 g_0 m_2/(4 m_1)) alpha (1+O(alpha^2)), beta-hat_12=-(9 g_0/4) alpha^(3/2)(1+O(alpha^2)), beta-hat_22=-(3 g_0 m_1/m_2) alpha^2 (1+O(alpha^2)), det beta-hat=-(117/16) g_0^2 alpha^3 (1+O(alpha^2)); for general axes by homogeneity (beta-hat(s a_1,s a_2)=s^(-2) beta-hat(a_1,a_2)) det beta-hat=-(117/16)(G/kappa)^2 a_1^3 a_2^(-7)(1+O(a_1^2/a_2^2)) as a_1/a_2->0 with m fixed
CONSTANT_SCOPE: O(.) constants and alpha_0 depend only on m_1/m_2
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p11b:as-in, stepP:p11b:as-pi, stepP:p11b:as-c, stepP:p11b:as-ent, stepP:p11b:as-det, bpP:p11b:beta-def, bpP:p11b:sec-set#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p11b:as-in | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:asymptotics@L240-L240 | proof step: inputs
EDGE: stepP:p11b:as-pi | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:asymptotics@L243-L243 | proof step: projection
EDGE: stepP:p11b:as-c | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:asymptotics@L244-L244 | proof step: sizes of c_nu
EDGE: stepP:p11b:as-ent | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:asymptotics@L246-L246 | proof step: the entries
EDGE: stepP:p11b:as-det | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:asymptotics@L247-L247 | proof step: determinant
EDGE: bpP:p11b:beta-def | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:asymptotics@L233-L233 | beta-hat entries and det
EDGE: bpP:p11b:sec-set#data | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:asymptotics@L231-L231 | a_1, a_2, alpha, kappa
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p11b:as-in
KIND: step
TITLE: Inputs
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:as-in@L240-L242
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:as-in@L240-L242
CONTRACT_ID: stepP:p11b:as-in
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Lambda_1=m_1 sqrt(kappa alpha), Lambda_2=m_2 sqrt(kappa), pref=-G m_1 m_2; b_{3/2}^(1)=(3/2)alpha(1+O(alpha^2)), b_{3/2}^(2)=(15/8)alpha^2(1+O(alpha^2))
SOURCE_QUANTIFIERS: alpha small; m_1/m_2 fixed
SOURCE_CONCLUSION: a=(3/8)G m_1 m_2 alpha^2(1+O(alpha^2)), b=(15/32)G m_1 m_2 alpha^3(1+O(alpha^2)); Q_11=-a/Lambda_1=-(3 G m_2/(8 sqrt kappa)) alpha^(3/2)(1+O(alpha^2)), Q_22=-a/Lambda_2=-(3 G m_1/(8 sqrt kappa)) alpha^2(1+O(alpha^2)), Q_12=b/sqrt(Lambda_1 Lambda_2)=O(alpha^(11/4)); Delta_Q:=Q_11-Q_22=Q_11(1+O(alpha^(1/2))) is nonzero and negative for small alpha
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p8:laplace, bpP:p8:coeffs, bpP:p11b:sec-set#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p8:laplace | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:as-in@L240-L240 | series of b_{3/2}^(1), b_{3/2}^(2) for small alpha
EDGE: bpP:p8:coeffs | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:as-in@L240-L240 | a_12, b_12 and Q_ij=q_ij/sqrt(Lambda_i Lambda_j)
EDGE: bpP:p11b:sec-set#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:as-in@L240-L240 | Lambda_i, pref, alpha
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p11b:as-pi
KIND: step
TITLE: Projection
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:as-pi@L243-L243
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:as-pi@L243-L243
CONTRACT_ID: stepP:p11b:as-pi
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Q_ij of the inputs; R=sqrt(Delta_Q^2+4 Q_12^2)>=¦Delta_Q¦; sigma_2-sigma_1=R; Pi_1 entries
SOURCE_QUANTIFIERS: alpha small
SOURCE_CONCLUSION: pi_12=-Q_12/R, ¦pi_12¦<=¦Q_12¦/¦Delta_Q¦=O(alpha^(5/4)); 0<=pi_22<=Q_12^2/Delta_Q^2=O(alpha^(5/2)); pi_11=1-pi_22
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p11b:as-in, bpP:p11b:sec-beta#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p11b:as-in | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:as-pi@L243-L243 | Q_12=O(alpha^(11/4)) and Delta_Q=Q_11(1+O(alpha^(1/2)))
EDGE: bpP:p11b:sec-beta#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:as-pi@L243-L243 | pi_12=Q_12/(sigma_1-sigma_2), pi_22=(sigma_2-Q_22)/R from the definition of Pi_1
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p11b:as-c
KIND: step
TITLE: Sizes of $c_\nu$
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:as-c@L244-L245
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:as-c@L244-L245
CONTRACT_ID: stepP:p11b:as-c
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: eq:series (leading terms of A, B, p_nu); Lambda_1^2=m_1^2 kappa alpha, Lambda_2^2=m_2^2 kappa, Lambda_1 Lambda_2=m_1 m_2 kappa alpha^(1/2); pref=-G m_1 m_2
SOURCE_QUANTIFIERS: alpha small
SOURCE_CONCLUSION: p_1-A/4=-(3/32)alpha^2(1+O(alpha^2)), p_2-A/4=(3/8)alpha^2(1+..), p_3=(9/16)alpha^2(1+..), p_4=O(alpha^4), p_5-B/8=O(alpha^3), p_6-B/8=O(alpha^3); dividing by the Lambda powers: c_1=(3 g_0 m_2/(32 m_1))alpha(1+O(alpha^2)), c_2=-(3 g_0 m_1/(8 m_2))alpha^2(1+..), c_3=-(9 g_0/16)alpha^(3/2)(1+..), c_4=O(alpha^(7/2)), c_5=O(alpha^(9/4)), c_6=O(alpha^(11/4))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p11b:pair-jet, bpP:p11b:quartic-explicit, stepP:p11b:as-in, bpP:p11b:sec-set#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p11b:pair-jet | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:as-c@L244-L244 | eq:series: leading terms of A, B, p_nu
EDGE: bpP:p11b:quartic-explicit | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:as-c@L244-L244 | definition of c_nu from p_nu, A, B and Lambda powers
EDGE: stepP:p11b:as-in | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:as-c@L244-L244 | Lambda_i as functions of alpha
EDGE: bpP:p11b:sec-set#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:as-c@L244-L244 | pref
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p11b:as-ent
KIND: step
TITLE: The entries
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:as-ent@L246-L246
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:as-ent@L246-L246
CONTRACT_ID: stepP:p11b:as-ent
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Definition beta-def; bounds pi_12=O(alpha^(5/4)), pi_11 pi_22=pi_12^2=O(alpha^(5/2)), delta_pi^2=1-4 pi_12^2; sizes of c_nu
SOURCE_QUANTIFIERS: alpha small
SOURCE_CONCLUSION: a=c_1+O(alpha^(7/2)), d=c_2+O(alpha^4), b=c_3+O(alpha^(7/2)); relative errors O(alpha^(5/2)), O(alpha^2), O(alpha^2); hence beta-hat_11=8a, beta-hat_12=4b, beta-hat_22=8d give the three limits
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p11b:beta-def, stepP:p11b:as-pi, stepP:p11b:as-c, bpP:p11b:sec-beta#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p11b:beta-def | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:as-ent@L246-L246 | a, d, b and beta-hat in terms of c_nu and pi_ij
EDGE: stepP:p11b:as-pi | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:as-ent@L246-L246 | bounds on pi_ij
EDGE: stepP:p11b:as-c | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:as-ent@L246-L246 | sizes of c_nu
EDGE: bpP:p11b:sec-beta#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:as-ent@L246-L246 | Uses pi_11 pi_22=pi_12^2 and the projection identities directly in the error estimates.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b+sol-review-P-m
REVIEWER: sol-delta-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p11b:as-det
KIND: step
TITLE: Determinant
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:as-det@L247-L247
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:as-det@L247-L247
CONTRACT_ID: stepP:p11b:as-det
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the three limits for beta-hat_ij; det beta-hat=64 a d-16 b^2; homogeneity: S_12 homogeneous of degree -1 in the lengths, actions scale as Lambda->s^(1/2)Lambda
SOURCE_QUANTIFIERS: alpha small; then general axes
SOURCE_CONCLUSION: det beta-hat=g_0^2 alpha^3[64(3/32)(-3/8)-16(81/256)](1+O(alpha^2))=-(117/16)g_0^2 alpha^3(1+O(alpha^2)) (the two summands have the same sign, no cancellation); homogeneity gives beta-hat(s a)=s^(-2) beta-hat(a) and the statement for general axes
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p11b:as-ent, bpP:p11b:beta-def, bpP:p11b:quartic-explicit
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p11b:as-ent | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:as-det@L247-L247 | the three entries
EDGE: bpP:p11b:beta-def | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:as-det@L247-L247 | det beta-hat=64 a d-16 b^2
EDGE: bpP:p11b:quartic-explicit | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:as-det@L247-L247 | c_nu with pref=-G m_1 m_2/a_2 and p_nu depending on alpha only give the scaling
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p11b:torsion
KIND: theorem
TITLE: $\det\hat\beta\not\equiv0$ and the torsion theorem
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:torsion@L250-L253
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:torsion@L254-L258
CONTRACT_ID: bpP:p11b:torsion
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n=2, G, m0>0, m_1, m_2>0; A_2={0<a_1<a_2} (connected, convex); Phi_4 of Definition good
SOURCE_QUANTIFIERS: G, m0, m_1, m_2
SOURCE_CONCLUSION: det beta-hat is real analytic on A_2 and not identically zero; hence {det beta-hat!=0} is open, dense and of full Lebesgue measure in A_2; the same for {Phi_4 det beta-hat!=0}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p11b:to-an, stepP:p11b:to-pt, stepP:p11b:to-id, bpP:p11b:beta-def, bpP:p9:good, bpP:p11b:sec-set#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p11b:to-an | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:torsion@L255-L255 | proof step: analyticity
EDGE: stepP:p11b:to-pt | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:torsion@L256-L256 | proof step: a point
EDGE: stepP:p11b:to-id | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:torsion@L257-L257 | proof step: identity theorem
EDGE: bpP:p11b:beta-def | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:torsion@L251-L251 | det beta-hat
EDGE: bpP:p9:good | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:torsion@L251-L251 | Phi_4
EDGE: bpP:p11b:sec-set#data | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:torsion@L251-L251 | A_2
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p11b:to-an
KIND: step
TITLE: Analyticity
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:to-an@L255-L255
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:to-an@L255-L255
CONTRACT_ID: stepP:p11b:to-an
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: entries of beta-hat real analytic on A_2 (Definition beta-def)
SOURCE_QUANTIFIERS: a in A_2
SOURCE_CONCLUSION: det beta-hat is real analytic on A_2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p11b:beta-def
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p11b:beta-def | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:to-an@L255-L255 | entries of beta-hat are real analytic on A_2
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p11b:to-pt
KIND: step
TITLE: A point
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:to-pt@L256-L256
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:to-pt@L256-L256
CONTRACT_ID: stepP:p11b:to-pt
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Proposition asymptotics with a_2=1, a_1=alpha small
SOURCE_QUANTIFIERS: alpha small
SOURCE_CONCLUSION: det beta-hat<0 at such a point, so det beta-hat is not identically zero
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p11b:asymptotics
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p11b:asymptotics | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:to-pt@L256-L256 | det beta-hat=-(117/16)g_0^2 alpha^3(1+O(alpha^2))<0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepP:p11b:to-id
KIND: step
TITLE: Identity theorem
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:to-id@L257-L257
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:to-id@L257-L257
CONTRACT_ID: stepP:p11b:to-id
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: det beta-hat analytic and not identically zero on connected A_2; Phi_4 not identically zero on A_2 (Theorem bpP:p10:good-point)
SOURCE_QUANTIFIERS: A_2
SOURCE_CONCLUSION: the zero set of det beta-hat is closed with empty interior and null (identity theorem); together with Phi_4 not identically zero on A_2 (Theorem good-point), Lemma generic gives that {Phi_4 det beta-hat!=0} is open, dense and of full measure
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p9:e-id, bpP:p10:good-point, bpP:p10:generic, stepP:p11b:to-an, stepP:p11b:to-pt, bpP:p11b:sec-set#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p9:e-id | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:to-id@L257-L257 | identity theorem on connected A_2 (alias e-id of this part)
EDGE: bpP:p10:good-point | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:to-id@L257-L257 | Phi_4 not identically zero on A_2
EDGE: bpP:p10:generic | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:to-id@L257-L257 | finite product of nonzero analytic functions
EDGE: stepP:p11b:to-an | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:to-id@L257-L257 | det beta-hat analytic
EDGE: stepP:p11b:to-pt | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:to-id@L257-L257 | det beta-hat not identically zero
EDGE: bpP:p11b:sec-set#data | blueprint-P/parts/p11b-planar-torsion.tex#stepP:p11b:to-id@L257-L257 | A_2 connected convex
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b
REVIEWER: sol-review-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p11b:patch
KIND: corollary
TITLE: Patches near every axis vector
STATEMENT_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:patch@L260-L262
PROOF_SOURCE: blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:patch@L263-L265
CONTRACT_ID: bpP:p11b:patch
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n=2; a* in A_2; eta>0
SOURCE_QUANTIFIERS: a* in A_2, eta>0; then a_0, r_0
SOURCE_CONCLUSION: there are a_0 in A_2 and r_0>0 with closed B_inf(a_0,2 r_0) subset B_inf(a*,eta) cap {Phi_4!=0} cap {det beta-hat!=0}; then B:=min over closed B_inf(a_0,r_0) of ¦det beta-hat¦>0, beta-hat is symmetric and Theorem birkhoff-form applies with K_a=closed B_inf(a_0,r_0), O_a=B_inf(a_0,2 r_0) (a cube: simply connected); moreover Part 10 frequency data (Theorem bpP:p10:interface) can be taken on the same patch
CONSTANT_SCOPE: a_0, r_0 depend on (G, m0, m, a*, eta)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p11b:torsion, bpP:p11b:birkhoff-form, bpP:p11b:beta-def, bpP:p9:good, bpP:p11b:sec-set#data, bpP:p10:interface
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p11b:torsion | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:patch@L264-L264 | {Phi_4 det beta-hat!=0} open and dense
EDGE: bpP:p11b:birkhoff-form | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:patch@L261-L261 | theorem applies with K_a, O_a
EDGE: bpP:p11b:beta-def | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:patch@L261-L261 | beta-hat symmetric, det beta-hat
EDGE: bpP:p9:good | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:patch@L261-L261 | {Phi_4!=0}
EDGE: bpP:p11b:sec-set#data | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:patch@L260-L260 | A_2
EDGE: bpP:p10:interface | blueprint-P/parts/p11b-planar-torsion.tex#bpP:p11b:patch@L260-L262 | The last sentence takes the Part 10 frequency data on this same patch, using the extra analytic nonvanishing condition det beta-hat != 0.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p11b+sol-review-P-l
REVIEWER: sol-delta-P-m
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The last sentence is part of the retained source conclusion and explicitly invokes interface. Part 12 uses only the good-patch clauses, but that does not erase a direct dependency of this full corollary. Keep the full source statement and the direct edge; no P-FIXED theorem is thereby added as a root.

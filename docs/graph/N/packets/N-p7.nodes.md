NODE: bpN:p7:ext-banach
KIND: external
TITLE: Banach fixed point theorem
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#bpN:p7:ext-banach@L17-L17
PROOF_SOURCE: -
CONTRACT_ID: bpN:p7:ext-banach
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: nonempty closed subset X of R^N; T:X->X a contraction
SOURCE_QUANTIFIERS: N; X; T
SOURCE_CONCLUSION: T has a fixed point (Mathlib ContractingWith.exists_fixedPoint)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7
REVIEWER: sol-review-N-d
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external (E1) of Part 7

NODE: bpN:p7:ext-taylor
KIND: external
TITLE: Taylor, Lagrange form, order one
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#bpN:p7:ext-taylor@L18-L18
PROOF_SOURCE: -
CONTRACT_ID: bpN:p7:ext-taylor
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: phi:[0,1]->R of class C^2
SOURCE_QUANTIFIERS: phi
SOURCE_CONCLUSION: phi(1)=phi(0)+phi'(0)+phi''(xi)/2 for some xi in (0,1) (Lagrange form, order one; Mathlib taylor_mean_remainder_lagrange)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7
REVIEWER: sol-review-N-d
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external (E2) of Part 7

NODE: bpN:p7:ext-num
KIND: external
TITLE: Numerics
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#bpN:p7:ext-num@L19-L19
PROOF_SOURCE: -
CONTRACT_ID: bpN:p7:ext-num
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: a,b real and c>0 for Young; x>=0 for x exp(-x)<=exp(-1); the displayed numerical constants are fixed
SOURCE_CONCLUSION: e>2.7, so 1/(12e)<0.0307, 6/(5e)<0.442, 15e/192>1/5; Young: ab<=a^2/(2c)+c b^2/2 (c>0); x e^{-x}<=e^{-1} for x>=0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external (E3) of Part 7 (numerics)

NODE: bpN:p7:ext-linalg
KIND: external
TITLE: Orthogonal projections
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#bpN:p7:ext-linalg@L20-L20
PROOF_SOURCE: -
CONTRACT_ID: bpN:p7:ext-linalg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: subspace E of R^n with orthogonal projection Pi and Pi^perp=1-Pi
SOURCE_QUANTIFIERS: E; Pi; u, v
SOURCE_CONCLUSION: Pi self-adjoint, ‖Pi v‖_2<=‖v‖_2, <u,Pi v>=<Pi u,v>, ‖Pi v‖_2=dist_2(v,E^perp)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7
REVIEWER: sol-review-N-d
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external (E4) of Part 7

NODE: bpN:p7:setting
KIND: definition
TITLE: Real neighbourhoods, real systems, orbits
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#bpN:p7:setting@L26-L32
PROOF_SOURCE: -
CONTRACT_ID: bpN:p7:setting
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: D subset R^n; rho,s>0; for the Hamiltonians: G in O(r,s)^R; h holomorphic on V_rD and real on U_rD
SOURCE_QUANTIFIERS: D; rho; s; r; G; J; z
SOURCE_CONCLUSION: defines U_rho D=V_rho D∩R^n={I in R^n: exists J in D, |I-J|<rho} (open); W_rho=R^n×U_rho D open in R^{2n}, equal to D_{rho,s}∩R^{2n}, W_rho⊂W_r for rho<=r; O(r,s)^R (G real on W_r); the real Hamiltonian G^R (=G on W_r, 0 elsewhere); a G-orbit in W_rho on J is z:R->R^{2n} with IsSolIn X_{G^R} W_rho J z; I(t)=z(t)_2; h_R=h|U_rD, omega=∇h_R (=∂_I h), Q(I)=D^2 h_R(I)
CONSTANT_SCOPE: no constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p4:domains, bpN:p4:norm, bpN:p3:gen-sol, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p4:domains | blueprint-N/parts/p7-stability.tex#bpN:p7:setting@L27-L27 | V_rho D, openness, D_{rho,s}
EDGE: bpN:p4:norm | blueprint-N/parts/p7-stability.tex#bpN:p7:setting@L28-L28 | class O(r,s) and reality on W_r
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p7-stability.tex#bpN:p7:setting@L29-L29 | IsSolIn F W J z
EDGE: bpN:p5:setting | blueprint-N/parts/p7-stability.tex#bpN:p7:setting@L29-L29 | X_{G^R}=J∇G^R, the frozen Hamiltonian field
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7
REVIEWER: sol-review-N-d
LEAN_STATUS: PROVED
LEAN_REF: cpx, realNbhd, realStrip, realH, IsOrbit, reMap, thetaGradR, hessR (KAM/Nekhoroshev/Stability/Setting.lean)
LEAN_NOTE: audit S7-1 PASS WITH NOTES
NOTE: package (standing-data definition) of Part 7: U_rho D, W_rho, O(r,s)^R, G^R, orbits, h_R, omega, Q; dropped candidate edges: Remark p3:totality (justification of the total convention, no fact consumed) and K:hamiltonian-real (\source provenance)

NODE: bpN:p7:real-system
KIND: lemma
TITLE: Holomorphic real systems
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#bpN:p7:real-system@L34-L37
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#bpN:p7:real-system@L38-L42
CONTRACT_ID: bpN:p7:real-system
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: G in O(r,s)^R; 0<rho<=r
SOURCE_QUANTIFIERS: G; rho
SOURCE_CONCLUSION: (a) G^R is C^infty on W_r and G^R(theta+k,I)=G^R(theta,I); (b) at x in W_r, G^R is differentiable and X_{G^R}(x)=X_G(x)=((∂_{I_i}G(x))_i,(-∂_{theta_i}G(x))_i) in R^{2n}; (c) X_{G^R} is C^1 on W_r and 1-periodic in theta; (d) Theorems ham-energy, gen-uniqueness, gen-maximal, Corollary gen-continuation-periodic and Lemma gen-exit apply to F=X_{G^R} on the open set W_rho; in particular G^R is constant along every G-orbit (energy conservation)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p7:rs-smooth, stepN:p7:rs-field, bpN:p7:setting, bpN:p3:ham-smooth, bpN:p3:ham-energy, bpN:p3:gen-uniqueness, bpN:p3:gen-maximal, bpN:p3:gen-continuation-periodic, bpN:p3:gen-exit, bpN:p4:norm, bpN:p4:domains, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p7:rs-smooth | blueprint-N/parts/p7-stability.tex#bpN:p7:real-system@L39-L39 | proof step
EDGE: stepN:p7:rs-field | blueprint-N/parts/p7-stability.tex#bpN:p7:real-system@L40-L40 | proof step
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#bpN:p7:real-system@L35-L35 | W_r, O(r,s)^R, G^R, G-orbits
EDGE: bpN:p3:ham-smooth | blueprint-N/parts/p7-stability.tex#bpN:p7:real-system@L41-L41 | step (d): G^R is C^2 on the open set W_rho, hence the cited results apply
EDGE: bpN:p3:ham-energy | blueprint-N/parts/p7-stability.tex#bpN:p7:real-system@L35-L35 | (d) energy conservation along orbits
EDGE: bpN:p3:gen-uniqueness | blueprint-N/parts/p7-stability.tex#bpN:p7:real-system@L35-L35 | (d) applicability of the uniqueness theorem
EDGE: bpN:p3:gen-maximal | blueprint-N/parts/p7-stability.tex#bpN:p7:real-system@L35-L35 | (d) applicability of the maximal-solution theorem
EDGE: bpN:p3:gen-continuation-periodic | blueprint-N/parts/p7-stability.tex#bpN:p7:real-system@L35-L35 | (d) applicability of the periodic continuation corollary
EDGE: bpN:p3:gen-exit | blueprint-N/parts/p7-stability.tex#bpN:p7:real-system@L35-L35 | (d) applicability of the exit lemma
EDGE: bpN:p4:norm | blueprint-N/parts/p7-stability.tex#bpN:p7:real-system@L35-L35 | the consumer uses O(r,s), Fourier coefficients or the weighted norm directly
EDGE: bpN:p4:domains | blueprint-N/parts/p7-stability.tex#bpN:p7:real-system@L39-L39 | the smoothness proof uses the open domain D_{r,s}
EDGE: bpN:p5:setting | blueprint-N/parts/p7-stability.tex#bpN:p7:real-system@L35-L35 | the consumer uses X_G or the symplectic matrix J directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: real_system (KAM/Nekhoroshev/Stability/RealSystem.lean)
LEAN_NOTE: audit S7-1 PASS WITH NOTES
NOTE: the unlabelled proofstep (d) at L41 has no node (SPEC); its references are attributed here. Dropped candidate edges: p1:holo-real (special case named in \source) and the K imports (used in the steps)

NODE: stepN:p7:rs-smooth
KIND: step
TITLE: Smoothness
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:rs-smooth@L39-L39
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:rs-smooth@L39-L39
CONTRACT_ID: stepN:p7:rs-smooth
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: G holomorphic on D_{r,s}; W_r=iota^{-1}(D_{r,s})
SOURCE_QUANTIFIERS: G
SOURCE_CONCLUSION: G^R in C^infty(W_r) (G^R=G∘iota, D^k G^R=D^k G∘iota on real vectors); periodicity inherited from O(r,s)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p1:holomorphic-regularity, bpN:p1:ext-restrict, bpN:p7:setting, bpN:p4:norm, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p1:holomorphic-regularity | blueprint-N/parts/p7-stability.tex#stepN:p7:rs-smooth@L39-L39 | holomorphic implies C^infty in the real sense
EDGE: bpN:p1:ext-restrict | blueprint-N/parts/p7-stability.tex#stepN:p7:rs-smooth@L39-L39 | real derivative of the restriction to R^{2n}
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:rs-smooth@L39-L39 | W_r, G^R
EDGE: bpN:p4:norm | blueprint-N/parts/p7-stability.tex#stepN:p7:rs-smooth@L39-L39 | periodicity in the class O(r,s)
EDGE: bpN:p4:domains | blueprint-N/parts/p7-stability.tex#stepN:p7:rs-smooth@L39-L39 | the consumer uses V_rD, D_{r,s} or a strip directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: real_system (KAM/Nekhoroshev/Stability/RealSystem.lean)
LEAN_NOTE: audit S7-1 PASS WITH NOTES, rows real-system(a) realH_contDiffOn (RealSystem:41), realH_periodic (RealSystem:52) at S7-1-audit-1.md:78 and S7-1-audit-1.md:79; real_system row S7-1-audit-1.md:69.
NOTE: -

NODE: stepN:p7:rs-field
KIND: step
TITLE: Field
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:rs-field@L40-L40
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:rs-field@L40-L40
CONTRACT_ID: stepN:p7:rs-field
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: G holomorphic on V=D_{r,s}, real at real points; rs-smooth
SOURCE_QUANTIFIERS: G
SOURCE_CONCLUSION: G^R agrees with Re G near each real point so X_{G^R}=X_G on W_r; the field is C^1 (ham-smooth) and periodic ((a) and ham-periodic)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p1:hamiltonian-real, bpN:p3:ham-smooth, bpN:p3:ham-periodic, stepN:p7:rs-smooth, bpN:p7:setting, bpN:p5:setting, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p1:hamiltonian-real | blueprint-N/parts/p7-stability.tex#stepN:p7:rs-field@L40-L40 | X_{G^R}=X_G from reality at real points of an open set
EDGE: bpN:p3:ham-smooth | blueprint-N/parts/p7-stability.tex#stepN:p7:rs-field@L40-L40 | C^1 regularity of the field
EDGE: bpN:p3:ham-periodic | blueprint-N/parts/p7-stability.tex#stepN:p7:rs-field@L40-L40 | periodicity of the field
EDGE: stepN:p7:rs-smooth | blueprint-N/parts/p7-stability.tex#stepN:p7:rs-field@L40-L40 | (a): smoothness and periodicity of G^R
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:rs-field@L40-L40 | W_r, G^R
EDGE: bpN:p5:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:rs-field@L40-L40 | X_G=J∇G
EDGE: bpN:p4:domains | blueprint-N/parts/p7-stability.tex#stepN:p7:rs-field@L40-L40 | the consumer uses V_rD, D_{r,s} or a strip directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: real_system (KAM/Nekhoroshev/Stability/RealSystem.lean)
LEAN_NOTE: audit S7-1 PASS WITH NOTES, row real_system (RealSystem:69: real/complex field identity, C1 field, interval energy) at S7-1-audit-1.md:69; frozen sign/slot check at S7-1-audit-1.md:116.
NOTE: -

NODE: bpN:p7:theta-derivative
KIND: lemma
TITLE: Derivative bound at real points
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#bpN:p7:theta-derivative@L44-L47
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#bpN:p7:theta-derivative@L48-L51
CONTRACT_ID: bpN:p7:theta-derivative
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u in O(rho,s) with finite norm
SOURCE_QUANTIFIERS: u; theta in R^n; I in U_rho D
SOURCE_CONCLUSION: sum_j |∂_{theta_j}u(theta,I)|<=|u|_{rho,s}/(e s), in particular ‖∂_theta u(theta,I)‖_2<=|u|_{rho,s}/(es); also |u(x)|<=|u|_{rho,s} on D_{rho,s}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p7:td-loss, stepN:p7:td-lim, bpN:p4:norm, bpN:p7:setting, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p7:td-loss | blueprint-N/parts/p7-stability.tex#bpN:p7:theta-derivative@L49-L49 | proof step
EDGE: stepN:p7:td-lim | blueprint-N/parts/p7-stability.tex#bpN:p7:theta-derivative@L50-L50 | proof step
EDGE: bpN:p4:norm | blueprint-N/parts/p7-stability.tex#bpN:p7:theta-derivative@L45-L45 | class O(rho,s) and norm
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#bpN:p7:theta-derivative@L45-L45 | U_rho D
EDGE: bpN:p4:domains | blueprint-N/parts/p7-stability.tex#bpN:p7:theta-derivative@L45-L45 | the consumer uses V_rD, D_{r,s} or a strip directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: theta_derivative (KAM/Nekhoroshev/Stability/Gradient.lean)
LEAN_NOTE: audit S7-2 PASS WITH NOTES
NOTE: -

NODE: stepN:p7:td-loss
KIND: step
TITLE: Strip loss
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:td-loss@L49-L49
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:td-loss@L49-L49
CONTRACT_ID: stepN:p7:td-loss
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u in O(rho,s) finite norm; 0<s'<s; fixed I
SOURCE_QUANTIFIERS: s'
SOURCE_CONCLUSION: sum_j |∂_{theta_j}u|_{I,s'}<=|u|_{I,s}/(e(s-s')) and |v(theta,I)|<=|v|_{I,s'} for theta in T_{s'}⊃R^n
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p4:b3-a, bpN:p4:cauchy, stepN:p4:b1-a, bpN:p4:sup-weighted, bpN:p4:norm, bpN:p4:domains, bpN:p7:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p4:b3-a | blueprint-N/parts/p7-stability.tex#stepN:p7:td-loss@L49-L49 | Cauchy estimate in the angle strip (Cauchy lemma (a))
EDGE: bpN:p4:cauchy | blueprint-N/parts/p7-stability.tex#stepN:p7:td-loss@L49-L49 | Lemma cauchy(a) pointwise in I
EDGE: stepN:p4:b1-a | blueprint-N/parts/p7-stability.tex#stepN:p7:td-loss@L49-L49 | pointwise bound by the weighted norm
EDGE: bpN:p4:sup-weighted | blueprint-N/parts/p7-stability.tex#stepN:p7:td-loss@L49-L49 | sup bound by the weighted norm
EDGE: bpN:p4:norm | blueprint-N/parts/p7-stability.tex#stepN:p7:td-loss@L49-L49 | the consumer uses O(r,s), Fourier coefficients or the weighted norm directly
EDGE: bpN:p4:domains | blueprint-N/parts/p7-stability.tex#stepN:p7:td-loss@L49-L49 | the consumer uses V_rD, D_{r,s} or a strip directly
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:td-loss@L49-L49 | the consumer uses W_r, U_rD, real Hamiltonians/orbits, omega or Q directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: theta_derivative (KAM/Nekhoroshev/Stability/Gradient.lean)
LEAN_NOTE: audit S7-2 PASS WITH NOTES, row theta_derivative (Gradient:60) at S7-2-audit-1.md:34 and proof paragraph (L73 sum at fixed action; L81 representation at positive width s') at S7-2-audit-1.md:46.
NOTE: -

NODE: stepN:p7:td-lim
KIND: step
TITLE: Limit
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:td-lim@L50-L50
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:td-lim@L50-L50
CONTRACT_ID: stepN:p7:td-lim
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n>=1; D subset R^n; varrho,s>0; u in O(varrho,s) with finite norm, as in theta-derivative; theta in R^n and I in U_varrho D for the derivative bound; x in D_{varrho,s} for the last value bound; 0<s'<s is the auxiliary limit parameter
SOURCE_QUANTIFIERS: s'↓0
SOURCE_CONCLUSION: letting s'↓0 gives the bound at real theta; ‖v‖_2<=sum_j|v_j|; the last claim |u(x)|<=|u|_{rho,s} is sup-weighted(a)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p7:td-loss, bpN:p1:ext-norms, bpN:p4:sup-weighted, bpN:p4:norm, bpN:p7:setting, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p7:td-loss | blueprint-N/parts/p7-stability.tex#stepN:p7:td-lim@L50-L50 | the bound for each s'
EDGE: bpN:p1:ext-norms | blueprint-N/parts/p7-stability.tex#stepN:p7:td-lim@L50-L50 | ‖v‖_2<=sum_j¦v_j¦
EDGE: bpN:p4:sup-weighted | blueprint-N/parts/p7-stability.tex#stepN:p7:td-lim@L50-L50 | ¦u(x)¦<=¦u¦_{rho,s}
EDGE: bpN:p4:norm | blueprint-N/parts/p7-stability.tex#stepN:p7:td-lim@L50-L50 | the consumer uses O(r,s), Fourier coefficients or the weighted norm directly
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:td-lim@L50-L50 | the derivative bound is at real theta and I in U_varrho D, the real neighbourhood fixed by this package
EDGE: bpN:p4:domains | blueprint-N/parts/p7-stability.tex#stepN:p7:td-lim@L50-L50 | the last claim is for x in D_{varrho,s}, the complex domain in the enclosing statement
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7+sol-delta2-N-d
REVIEWER: sol-delta3-N-a
LEAN_STATUS: PROVED
LEAN_REF: theta_derivative (KAM/Nekhoroshev/Stability/Gradient.lean)
LEAN_NOTE: audit S7-2 PASS WITH NOTES, proof paragraph at S7-2-audit-1.md:46: L88-98 takes s' down to 0 on the numerical bound, Euclidean comparison euclid_le_sum_norm (L48) and complex-domain value estimate.
NOTE: -

NODE: bpN:p7:resonant-gradient
KIND: lemma
TITLE: Resonant gradients lie in the span of $\Lambda$
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#bpN:p7:resonant-gradient@L53-L56
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#bpN:p7:resonant-gradient@L57-L60
CONTRACT_ID: bpN:p7:resonant-gradient
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Lambda subset Z^n; Pi=Pi_Lambda the Euclidean orthogonal projection onto span_R Lambda; g in O(r,s)^R with finite norm and P_Lambda g=g
SOURCE_QUANTIFIERS: Lambda; g
SOURCE_CONCLUSION: Pi^perp ∂_theta g(theta,I)=0, i.e. ∂_theta g(theta,I) in ran Pi, for all (theta,I) in W_r
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p7:rg-coef, stepN:p7:rg-zero, bpN:p7:setting, bpN:p4:norm, bpN:p4:projections
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p7:rg-coef | blueprint-N/parts/p7-stability.tex#bpN:p7:resonant-gradient@L58-L58 | proof step
EDGE: stepN:p7:rg-zero | blueprint-N/parts/p7-stability.tex#bpN:p7:resonant-gradient@L59-L59 | proof step
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#bpN:p7:resonant-gradient@L54-L54 | W_r, O(r,s)^R
EDGE: bpN:p4:norm | blueprint-N/parts/p7-stability.tex#bpN:p7:resonant-gradient@L54-L54 | norm and class
EDGE: bpN:p4:projections | blueprint-N/parts/p7-stability.tex#bpN:p7:resonant-gradient@L54-L54 | P_Lambda g=g
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7
REVIEWER: sol-review-N-d
LEAN_STATUS: PROVED
LEAN_REF: resSpan, resonant_gradient (KAM/Nekhoroshev/Stability/Gradient.lean)
LEAN_NOTE: audit S7-2 PASS WITH NOTES
NOTE: -

NODE: stepN:p7:rg-coef
KIND: step
TITLE: Coefficients
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:rg-coef@L58-L58
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:rg-coef@L58-L58
CONTRACT_ID: stepN:p7:rg-coef
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: g with P_Lambda g=g; u=Pi^perp ∂_theta g
SOURCE_QUANTIFIERS: k in Z^n
SOURCE_CONCLUSION: the components of u are finite combinations of ∂_{theta_j}g in O(r,s) with coefficients uhat_k=2πi Pi^perp k ghat_k=0: for k in Lambda Pi^perp k=0, for k not in Lambda ghat_k=0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p4:coefficients, bpN:p4:projections, bpN:p4:norm, bpN:p7:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p4:coefficients | blueprint-N/parts/p7-stability.tex#stepN:p7:rg-coef@L58-L58 | (b) Fourier coefficients of the derivatives
EDGE: bpN:p4:projections | blueprint-N/parts/p7-stability.tex#stepN:p7:rg-coef@L58-L58 | ghat_k=0 for k not in Lambda when g=P_Lambda g
EDGE: bpN:p4:norm | blueprint-N/parts/p7-stability.tex#stepN:p7:rg-coef@L58-L58 | the consumer uses O(r,s), Fourier coefficients or the weighted norm directly
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:rg-coef@L58-L58 | the consumer uses W_r, U_rD, real Hamiltonians/orbits, omega or Q directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: resonant_gradient (KAM/Nekhoroshev/Stability/Gradient.lean)
LEAN_NOTE: audit S7-2 PASS WITH NOTES, rows sum_dtheta_eq_zero (Gradient:124) and resonant_gradient (Gradient:166) at S7-2-audit-1.md:37; proof paragraph L130-164 (each Fourier term vanishes by orthogonality or off-support) at S7-2-audit-1.md:48.
NOTE: -

NODE: stepN:p7:rg-zero
KIND: step
TITLE: Vanishing
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:rg-zero@L59-L59
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:rg-zero@L59-L59
CONTRACT_ID: stepN:p7:rg-zero
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: uhat_k=0 for all k (rg-coef)
SOURCE_QUANTIFIERS: s'<s
SOURCE_CONCLUSION: u has finite norm at width s' (Cauchy), so u=sum uhat_k chi_k=0 on D_{r,s'}, in particular at real points
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p4:cauchy, bpN:p4:coefficients, stepN:p7:rg-coef, bpN:p4:norm, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p4:cauchy | blueprint-N/parts/p7-stability.tex#stepN:p7:rg-zero@L59-L59 | (a): derivatives have finite norm at a smaller width
EDGE: bpN:p4:coefficients | blueprint-N/parts/p7-stability.tex#stepN:p7:rg-zero@L59-L59 | (d): coefficients determine the function
EDGE: stepN:p7:rg-coef | blueprint-N/parts/p7-stability.tex#stepN:p7:rg-zero@L59-L59 | vanishing coefficients
EDGE: bpN:p4:norm | blueprint-N/parts/p7-stability.tex#stepN:p7:rg-zero@L59-L59 | the consumer uses O(r,s), Fourier coefficients or the weighted norm directly
EDGE: bpN:p4:domains | blueprint-N/parts/p7-stability.tex#stepN:p7:rg-zero@L59-L59 | the consumer uses V_rD, D_{r,s} or a strip directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: resonant_gradient (KAM/Nekhoroshev/Stability/Gradient.lean)
LEAN_NOTE: audit S7-2 PASS WITH NOTES, proof paragraph at S7-2-audit-1.md:48 (L130-164 summable expansion at s/2 sums to zero; L173-196 annihilator argument gives span membership, equivalent to the source conclusion); row resonant_gradient S7-2-audit-1.md:38.
NOTE: -

NODE: bpN:p7:conjugation
KIND: lemma
TITLE: Conjugation of orbits
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#bpN:p7:conjugation@L64-L67
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#bpN:p7:conjugation@L68-L71
CONTRACT_ID: bpN:p7:conjugation
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: H in O(r,s)^R; H~ in O(r~,s~)^R; Psi:D_{r~,s~}->D_{r,s} holomorphic, real at real points, (DPsi)^T J DPsi=J, H~=H∘Psi; z~ an H~-orbit in W_r~ on J
SOURCE_QUANTIFIERS: H; H~; Psi; z~; J
SOURCE_CONCLUSION: z=Psi∘z~ is an H-orbit in W_r on J
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p7:cj-real, stepN:p7:cj-chain, bpN:p7:setting, bpN:p4:norm, bpN:p4:domains, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p7:cj-real | blueprint-N/parts/p7-stability.tex#bpN:p7:conjugation@L69-L69 | proof step
EDGE: stepN:p7:cj-chain | blueprint-N/parts/p7-stability.tex#bpN:p7:conjugation@L70-L70 | proof step
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#bpN:p7:conjugation@L65-L65 | orbits, O(r,s)^R, W_r
EDGE: bpN:p4:norm | blueprint-N/parts/p7-stability.tex#bpN:p7:conjugation@L65-L65 | the consumer uses O(r,s), Fourier coefficients or the weighted norm directly
EDGE: bpN:p4:domains | blueprint-N/parts/p7-stability.tex#bpN:p7:conjugation@L65-L65 | the consumer uses V_rD, D_{r,s} or a strip directly
EDGE: bpN:p5:setting | blueprint-N/parts/p7-stability.tex#bpN:p7:conjugation@L65-L65 | the consumer uses X_G or the symplectic matrix J directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: conjugation (KAM/Nekhoroshev/Stability/Conjugation.lean)
LEAN_NOTE: audit S7-3 PASS WITH NOTES
NOTE: -

NODE: stepN:p7:cj-real
KIND: step
TITLE: Real points
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:cj-real@L69-L69
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:cj-real@L69-L69
CONTRACT_ID: stepN:p7:cj-real
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Psi real at real points, symplectic
SOURCE_QUANTIFIERS: x in W_r~
SOURCE_CONCLUSION: Psi maps W_r~=D_{r~,s~}∩R^{2n} into W_r; the real derivative Y=DPsi(x) is the real restriction of the complex one and Y^T J Y=J; hence det Y=±1 and Y J Y^T=J
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p5:sy-conserve, bpN:p7:setting, bpN:p4:domains, bpN:p5:setting, bpN:p1:ext-restrict
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p5:sy-conserve | blueprint-N/parts/p7-stability.tex#stepN:p7:cj-real@L69-L69 | Y^T J Y=J implies Y J Y^T=J and det Y=±1
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:cj-real@L69-L69 | W_r~, W_r
EDGE: bpN:p4:domains | blueprint-N/parts/p7-stability.tex#stepN:p7:cj-real@L69-L69 | the consumer uses V_rD, D_{r,s} or a strip directly
EDGE: bpN:p5:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:cj-real@L69-L69 | the consumer uses X_G or the symplectic matrix J directly
EDGE: bpN:p1:ext-restrict | blueprint-N/parts/p7-stability.tex#stepN:p7:cj-real@L69-L69 | restriction of scalars and the inclusion chain rule apply on the open action-angle domain
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: BYPASSED
LEAN_REF: conjugation (KAM/Nekhoroshev/Stability/Conjugation.lean)
LEAN_NOTE: BYPASSED (D27): Lean conjugation (Conjugation.lean:89, audit S7-3 PASS WITH NOTES) does not form the real Jacobian Y with Y^T J Y = J and det Y=+-1; it works first with the complex field, proves Y J Y^T = J-type field identity via map_hamiltonianJ_comp from complex symplecticity, and restricts to reals via reMap_mem and reMap_hasFDerivAt (intertwining for every real direction) (S7-3-audit-1.md:142; note 3 at S7-3-audit-1.md:250). Route taken: conjugation.
NOTE: -

NODE: stepN:p7:cj-chain
KIND: step
TITLE: Chain rule
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:cj-chain@L70-L70
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:cj-chain@L70-L70
CONTRACT_ID: stepN:p7:cj-chain
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: cj-real; H~^R=H^R∘Psi on W_r~
SOURCE_QUANTIFIERS: t in J
SOURCE_CONCLUSION: grad H~^R(x)=Y^T grad H^R(Psi x) and d/dt Psi(z~)=Y z~'=Y J Y^T grad H^R(Psi z~)=X_{H^R}(Psi z~); z(t) in W_r
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p7:real-system, stepN:p7:cj-real, bpN:p5:setting, bpN:p7:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p7:real-system | blueprint-N/parts/p7-stability.tex#stepN:p7:cj-chain@L70-L70 | (b) X_{H^R}=J∇H^R at real points
EDGE: stepN:p7:cj-real | blueprint-N/parts/p7-stability.tex#stepN:p7:cj-chain@L70-L70 | Y J Y^T=J and Psi maps W_r~ into W_r
EDGE: bpN:p5:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:cj-chain@L70-L70 | X_u=J∇u
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:cj-chain@L70-L70 | orbits
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7
REVIEWER: sol-review-N-d
LEAN_STATUS: PROVED
LEAN_REF: conjugation (KAM/Nekhoroshev/Stability/Conjugation.lean)
LEAN_NOTE: audit S7-3 PASS WITH NOTES, row conjugation (Conjugation:89) at S7-3-audit-1.md:46 and proof paragraph at S7-3-audit-1.md:142: chain rule gives HasDerivAt of Psi o z~ with the H-field at every orbit time including endpoints, orbit in W_r.
NOTE: -

NODE: bpN:p7:preimage
KIND: lemma
TITLE: Real preimages of a near-identity map
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#bpN:p7:preimage@L73-L76
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#bpN:p7:preimage@L77-L83
CONTRACT_ID: bpN:p7:preimage
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: D subset R^n; r~,s~>0; Psi:D_{r~,s~}->C^{2n} holomorphic, real at real points; G=Psi-id with |G_theta|<=d_theta, |G_I|<=d_I on D_{r~,s~}; 0<rho'<=r~, 0<sigma'<=2s~ with kappa_*=max(d_theta/sigma',d_I/rho')<=1/4
SOURCE_QUANTIFIERS: D; r~; s~; Psi; d_theta; d_I; rho'; sigma'; y
SOURCE_CONCLUSION: for every y=(theta_y,I_y) in R^n×D there is x=(theta_x,I_x) in W_r~ with Psi(x)=y, |theta_x-theta_y|<=d_theta, |I_x-I_y|<=d_I
CONSTANT_SCOPE: none beyond the stated bounds
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p7:pi-set, stepN:p7:pi-self, stepN:p7:pi-contr, stepN:p7:pi-fix, bpN:p7:setting, bpN:p5:setting, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p7:pi-set | blueprint-N/parts/p7-stability.tex#bpN:p7:preimage@L79-L79 | proof step
EDGE: stepN:p7:pi-self | blueprint-N/parts/p7-stability.tex#bpN:p7:preimage@L80-L80 | proof step
EDGE: stepN:p7:pi-contr | blueprint-N/parts/p7-stability.tex#bpN:p7:preimage@L81-L81 | proof step
EDGE: stepN:p7:pi-fix | blueprint-N/parts/p7-stability.tex#bpN:p7:preimage@L82-L82 | proof step
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#bpN:p7:preimage@L74-L74 | W_r~, real points
EDGE: bpN:p5:setting | blueprint-N/parts/p7-stability.tex#bpN:p7:preimage@L78-L78 | scaled norm nu(a,b)=max(¦a¦/sigma',¦b¦/rho') of Definition p5:setting
EDGE: bpN:p4:domains | blueprint-N/parts/p7-stability.tex#bpN:p7:preimage@L74-L74 | the consumer uses V_rD, D_{r,s} or a strip directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: preimage (KAM/Nekhoroshev/Stability/Preimage.lean)
LEAN_NOTE: audit S7-4 PASS WITH NOTES
NOTE: -

NODE: stepN:p7:pi-set
KIND: step
TITLE: A closed convex set
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:pi-set@L79-L79
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:pi-set@L79-L79
CONTRACT_ID: stepN:p7:pi-set
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: nu(a,b)=max(|a|/sigma',|b|/rho'); kappa_*<=1/4; y in R^n×D
SOURCE_QUANTIFIERS: X
SOURCE_CONCLUSION: X={x in R^{2n}: nu(x-y)<=kappa_*} is closed, convex, nonempty; for x in X, |I_x-I_y|<=rho'/4<r~ and I_y in D, so x in W_r~
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p7:setting, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:pi-set@L79-L79 | W_r~=R^n×U_r~ D and U_r~ D
EDGE: bpN:p5:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:pi-set@L79-L79 | scaled norm nu
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7
REVIEWER: sol-review-N-d
LEAN_STATUS: PROVED
LEAN_REF: preimage (KAM/Nekhoroshev/Stability/Preimage.lean)
LEAN_NOTE: audit S7-4 PASS, row preimage and proof paragraph (L54-94 domain geometry: complex radius-1/2 ball inside domain at radius-1/4 real centres; convex closed ball X) at S7-4-audit-1.md:118 and S7-4-audit-1.md:129; Lean lines L114-227.
NOTE: -

NODE: stepN:p7:pi-self
KIND: step
TITLE: Self-map
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:pi-self@L80-L80
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:pi-self@L80-L80
CONTRACT_ID: stepN:p7:pi-self
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: pi-set; Psi real at real points; nu(G)<=kappa_*
SOURCE_QUANTIFIERS: T(x)=y-G(x)
SOURCE_CONCLUSION: T is real and nu(T(x)-y)=nu(G(x))<=kappa_*: T maps X into X
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p7:pi-set, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p7:pi-set | blueprint-N/parts/p7-stability.tex#stepN:p7:pi-self@L80-L80 | the set X
EDGE: bpN:p5:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:pi-self@L80-L80 | scaled norm nu
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7
REVIEWER: sol-review-N-d
LEAN_STATUS: PROVED
LEAN_REF: preimage (KAM/Nekhoroshev/Stability/Preimage.lean)
LEAN_NOTE: audit S7-4 PASS, proof paragraph at S7-4-audit-1.md:129 ('T u = Wy - psi u preserves X'), reality of T from real Psi; Lean preimage L114-227.
NOTE: -

NODE: stepN:p7:pi-contr
KIND: step
TITLE: Contraction
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:pi-contr@L81-L81
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:pi-contr@L81-L81
CONTRACT_ID: stepN:p7:pi-contr
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: pi-set, pi-self; G holomorphic with nu(G)<=kappa_*
SOURCE_QUANTIFIERS: x in X
SOURCE_CONCLUSION: the complex nu-ball of radius 1/2 about x lies in D_{r~,s~}; |DG(x)|_nu<=2kappa_*<=1/2 (general Cauchy); real derivative of G on R^{2n} is the restriction; mean value inequality on convex X gives nu(T(x)-T(x'))<=nu(x-x')/2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p4:general-cauchy, bpN:p1:ext-restrict, K:bp:p1:ext-mvt, stepN:p7:pi-set, stepN:p7:pi-self, bpN:p4:domains, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p4:general-cauchy | blueprint-N/parts/p7-stability.tex#stepN:p7:pi-contr@L81-L81 | Cauchy estimate with R=1/2 for the holomorphic G
EDGE: bpN:p1:ext-restrict | blueprint-N/parts/p7-stability.tex#stepN:p7:pi-contr@L81-L81 | real derivative of G¦_{R^{2n}} is the restriction
EDGE: K:bp:p1:ext-mvt | blueprint-N/parts/p7-stability.tex#stepN:p7:pi-contr@L81-L81 | mean value inequality on the convex set X
EDGE: stepN:p7:pi-set | blueprint-N/parts/p7-stability.tex#stepN:p7:pi-contr@L81-L81 | the convex set X
EDGE: stepN:p7:pi-self | blueprint-N/parts/p7-stability.tex#stepN:p7:pi-contr@L81-L81 | T:X->X
EDGE: bpN:p4:domains | blueprint-N/parts/p7-stability.tex#stepN:p7:pi-contr@L81-L81 | domain D_{r~,s~}, polydiscs
EDGE: bpN:p5:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:pi-contr@L81-L81 | scaled norm nu
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7
REVIEWER: sol-review-N-d
LEAN_STATUS: PROVED
LEAN_REF: preimage (KAM/Nekhoroshev/Stability/Preimage.lean)
LEAN_NOTE: audit S7-4 PASS, proof paragraph at S7-4-audit-1.md:126 (Cauchy ||DG||<=2 kappa at L158-161, real restriction and contractive real-part projection, mean value inequality on convex X, 2 kappa<=1/2) and domain inclusion L54-94 at S7-4-audit-1.md:118.
NOTE: -

NODE: stepN:p7:pi-fix
KIND: step
TITLE: Fixed point
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:pi-fix@L82-L82
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:pi-fix@L82-L82
CONTRACT_ID: stepN:p7:pi-fix
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: T a contraction of the closed convex set X into itself (pi-self, pi-contr)
SOURCE_QUANTIFIERS: x
SOURCE_CONCLUSION: Banach gives x=y-G(x), i.e. Psi(x)=x+G(x)=y; y-x=G(x) gives the displacement bounds
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p7:ext-banach, stepN:p7:pi-self, stepN:p7:pi-contr
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p7:ext-banach | blueprint-N/parts/p7-stability.tex#stepN:p7:pi-fix@L82-L82 | fixed point of the contraction T
EDGE: stepN:p7:pi-self | blueprint-N/parts/p7-stability.tex#stepN:p7:pi-fix@L82-L82 | T maps X into X
EDGE: stepN:p7:pi-contr | blueprint-N/parts/p7-stability.tex#stepN:p7:pi-fix@L82-L82 | T is a 1/2-contraction
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7
REVIEWER: sol-review-N-d
LEAN_STATUS: PROVED
LEAN_REF: preimage (KAM/Nekhoroshev/Stability/Preimage.lean)
LEAN_NOTE: audit S7-4 PASS, proof paragraph at S7-4-audit-1.md:129: Banach fixed point on complete nonempty X, reality recovers Psi(i x)=i y, displacement bounds from the original hypotheses.
NOTE: -

NODE: bpN:p7:preimage-nfl
KIND: corollary
TITLE: Preimages for the Normal Form Lemma
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#bpN:p7:preimage-nfl@L85-L87
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#bpN:p7:preimage-nfl@L88-L90
CONTRACT_ID: bpN:p7:preimage-nfl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Theorem normal-form with Lambda=-Lambda, h,f real on real points, kappa>=6; D subset R^n
SOURCE_QUANTIFIERS: as in normal-form
SOURCE_CONCLUSION: every y in R^n×D equals Psi(x) for some x in W_{r/2} with |I_x-I_y|<=qK eps/alpha (<=r/2^7)
CONSTANT_SCOPE: as in normal-form
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p7:pn-apply, bpN:p6:normal-form, bpN:p7:setting, bpN:p6:setting, bpN:p6#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p7:pn-apply | blueprint-N/parts/p7-stability.tex#bpN:p7:preimage-nfl@L89-L89 | proof step
EDGE: bpN:p6:normal-form | blueprint-N/parts/p7-stability.tex#bpN:p7:preimage-nfl@L86-L86 | hypotheses and the map Psi of the Normal Form Lemma
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#bpN:p7:preimage-nfl@L86-L86 | W_{r/2}, real points
EDGE: bpN:p6:setting | blueprint-N/parts/p7-stability.tex#bpN:p7:preimage-nfl@L86-L86 | the consumer assumes/uses the Part-6 resonant setting or nonresonance
EDGE: bpN:p6#data | blueprint-N/parts/p7-stability.tex#bpN:p7:preimage-nfl@L86-L86 | the consumer uses q, kappa or Z_K directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: preimage_nfl (KAM/Nekhoroshev/Stability/Preimage.lean)
LEAN_NOTE: audit S7-4 PASS WITH NOTES
NOTE: -

NODE: stepN:p7:pn-apply
KIND: step
TITLE: Apply Lemma~\ref{bpN:p7:preimage}
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:pn-apply@L89-L89
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:pn-apply@L89-L89
CONTRACT_ID: stepN:p7:pn-apply
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: normal-form hypotheses with (i); Psi real at real points; d_I=qK eps/alpha<=r/2^7; d_theta=10q eps/(2πalpha r)
SOURCE_QUANTIFIERS: r~=r/2, s~=s/6, rho'=r/2, sigma'=s/3
SOURCE_CONCLUSION: Lemma preimage applies: d_I/rho'<=1/64 and d_theta/sigma'=30q eps/(2π alpha r s)<=30/(2^7 kappa)<=30/768<1/4
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p7:preimage, bpN:p6:normal-form, bpN:p6#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p7:preimage | blueprint-N/parts/p7-stability.tex#stepN:p7:pn-apply@L89-L89 | conclusion with these data
EDGE: bpN:p6:normal-form | blueprint-N/parts/p7-stability.tex#stepN:p7:pn-apply@L89-L89 | (d) reality of Psi, (c) displacement bounds, hypothesis (i), (ii)
EDGE: bpN:p6#data | blueprint-N/parts/p7-stability.tex#stepN:p7:pn-apply@L89-L89 | kappa=2πKs, q
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7
REVIEWER: sol-review-N-d
LEAN_STATUS: PROVED
LEAN_REF: preimage_nfl (KAM/Nekhoroshev/Stability/Preimage.lean)
LEAN_NOTE: audit S7-4 PASS, row preimage_nfl and proof paragraph L245-271 (q>0, d_I/rho' <= 1/64 via qK eps/alpha <= r/128, angle ratio 30/(128 . 2 pi K s) <= 30/768 < 1/4) at S7-4-audit-1.md:135.
NOTE: -

NODE: bpN:p7:transfer
KIND: lemma
TITLE: Transfer of an a priori confinement through a symplectic map
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#bpN:p7:transfer@L92-L102
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#bpN:p7:transfer@L103-L108
CONTRACT_ID: bpN:p7:transfer
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: D subset R^n; H in O(r,s)^R; H~ in O(r~,s~)^R; Psi:D_{r~,s~}->D_{r,s} as in conjugation; |.|_* a norm on R^n with |.|<=|.|_*; (T1) |Pi_I Psi(x)-I_x|_*<=d_* for x in W_r~; (T2) every y in R^n×D equals Psi(x) for some x in W_r~; (T3) rho>0 with d_*+rho<r~ and T:D->(0,inf] such that for every I_y in D, interval J~∋0 and H~-orbit z~ in W_r~ on J~ with |I~(0)-I_y|_*<=d_*: |I~(t)-I~(0)|_*<=rho for t in J~, |t|<=T(I_y)
SOURCE_QUANTIFIERS: D; H; H~; Psi; |.|_*; d_*; rho; T; then J, z, I_y
SOURCE_CONCLUSION: for every interval J∋0 and every H-orbit z in W_r on J with I_y:=I(0) in D: |I(t)-I(0)|_*<=rho+2d_* for t in J, |t|<=T(I_y)
CONSTANT_SCOPE: d_*, rho, T are data of the hypotheses (T1)-(T3); T may depend on I_y
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p7:tr-orbit, stepN:p7:tr-long, stepN:p7:tr-ident, stepN:p7:tr-est, bpN:p7:conjugation, bpN:p7:setting, bpN:p4:norm, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p7:tr-orbit | blueprint-N/parts/p7-stability.tex#bpN:p7:transfer@L104-L104 | proof step
EDGE: stepN:p7:tr-long | blueprint-N/parts/p7-stability.tex#bpN:p7:transfer@L105-L105 | proof step
EDGE: stepN:p7:tr-ident | blueprint-N/parts/p7-stability.tex#bpN:p7:transfer@L106-L106 | proof step
EDGE: stepN:p7:tr-est | blueprint-N/parts/p7-stability.tex#bpN:p7:transfer@L107-L107 | proof step
EDGE: bpN:p7:conjugation | blueprint-N/parts/p7-stability.tex#bpN:p7:transfer@L93-L93 | Psi, H, H~ as in Lemma conjugation
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#bpN:p7:transfer@L93-L93 | orbits, W_r, O(r,s)^R
EDGE: bpN:p4:norm | blueprint-N/parts/p7-stability.tex#bpN:p7:transfer@L93-L93 | the consumer uses O(r,s), Fourier coefficients or the weighted norm directly
EDGE: bpN:p4:domains | blueprint-N/parts/p7-stability.tex#bpN:p7:transfer@L93-L93 | the consumer uses V_rD, D_{r,s} or a strip directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: transfer (KAM/Nekhoroshev/Stability/Transfer.lean)
LEAN_NOTE: audit S7-3 PASS WITH NOTES
NOTE: dropped candidate edge: p3:confinement-glue (\source: "so that Part 10 can connect it with existence": a forward pointer)

NODE: stepN:p7:tr-orbit
KIND: step
TITLE: A normal-form orbit
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:tr-orbit@L104-L104
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:tr-orbit@L104-L104
CONTRACT_ID: stepN:p7:tr-orbit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (T2); (T1); Psi
SOURCE_QUANTIFIERS: x; z~
SOURCE_CONCLUSION: choose x in W_r~ with Psi(x)=z(0), |I_x-I_y|_*<=d_*; z~ the maximal solution of X_{H~^R} in W_r~ through x on (T_-,T_+)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p7:real-system, bpN:p3:gen-maximal, bpN:p7:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p7:real-system | blueprint-N/parts/p7-stability.tex#stepN:p7:tr-orbit@L104-L104 | (d) applicability of the maximal-solution theorem to X_{H~^R} on W_r~
EDGE: bpN:p3:gen-maximal | blueprint-N/parts/p7-stability.tex#stepN:p7:tr-orbit@L104-L104 | existence of the maximal solution through x
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:tr-orbit@L104-L104 | orbits in W_r~
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7
REVIEWER: sol-review-N-d
LEAN_STATUS: PROVED
LEAN_REF: transfer (KAM/Nekhoroshev/Stability/Transfer.lean)
LEAN_NOTE: audit S7-3 PASS WITH NOTES, row transfer (Transfer:156) at S7-3-audit-1.md:48 and proof paragraph (Transfer 179-259: T2 initial preimage, T1 and norm symmetry, maximal H~ orbit by real_system(c)) at S7-3-audit-1.md:156.
NOTE: -

NODE: stepN:p7:tr-long
KIND: step
TITLE: It lives long enough
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:tr-long@L105-L105
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:tr-long@L105-L105
CONTRACT_ID: stepN:p7:tr-long
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (T3); tr-orbit; compact K={I:|I-I_x|_*<=rho}
SOURCE_QUANTIFIERS: t
SOURCE_CONCLUSION: {|t|<=T(I_y)}⊂(T_-,T_+): otherwise T_+<infinity with I~(t') in the compact K⊂U_r~ D, so T_+=infinity by periodic continuation, contradiction; likewise for t<=0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:gen-continuation-periodic, bpN:p7:real-system, stepN:p7:tr-orbit, bpN:p7:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:gen-continuation-periodic | blueprint-N/parts/p7-stability.tex#stepN:p7:tr-long@L105-L105 | a solution that stays in a compact subset of the base is global (periodic field)
EDGE: bpN:p7:real-system | blueprint-N/parts/p7-stability.tex#stepN:p7:tr-long@L105-L105 | (c) the field is periodic and C^1
EDGE: stepN:p7:tr-orbit | blueprint-N/parts/p7-stability.tex#stepN:p7:tr-long@L105-L105 | z~ with maximal interval (T_-,T_+)
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:tr-long@L105-L105 | U_r~ D, W_r~
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7
REVIEWER: sol-review-N-d
LEAN_STATUS: PROVED
LEAN_REF: transfer (KAM/Nekhoroshev/Stability/Transfer.lean)
LEAN_NOTE: audit S7-3 PASS WITH NOTES, proof paragraph at S7-3-audit-1.md:156: actions in compact K (closed Nrm ball), d+rho<r~, admissible time beyond a finite maximal endpoint contradicts periodic continuation.
NOTE: -

NODE: stepN:p7:tr-ident
KIND: step
TITLE: Identification
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:tr-ident@L106-L106
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:tr-ident@L106-L106
CONTRACT_ID: stepN:p7:tr-ident
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: tr-orbit; Lemma conjugation
SOURCE_QUANTIFIERS: z=Psi∘z~ on J∩(T_-,T_+)
SOURCE_CONCLUSION: Psi∘z~ is an H-orbit in W_r on (T_-,T_+) with value y at 0, as is z on J; uniqueness gives z=Psi∘z~ on J∩(T_-,T_+)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p7:conjugation, bpN:p3:gen-uniqueness, bpN:p7:real-system, stepN:p7:tr-orbit, bpN:p7:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p7:conjugation | blueprint-N/parts/p7-stability.tex#stepN:p7:tr-ident@L106-L106 | Psi∘z~ is an H-orbit
EDGE: bpN:p3:gen-uniqueness | blueprint-N/parts/p7-stability.tex#stepN:p7:tr-ident@L106-L106 | uniqueness with F=X_{H^R}, W=W_r
EDGE: bpN:p7:real-system | blueprint-N/parts/p7-stability.tex#stepN:p7:tr-ident@L106-L106 | (d) applicability of uniqueness
EDGE: stepN:p7:tr-orbit | blueprint-N/parts/p7-stability.tex#stepN:p7:tr-ident@L106-L106 | the orbit z~
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:tr-ident@L106-L106 | the consumer uses W_r, U_rD, real Hamiltonians/orbits, omega or Q directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: transfer (KAM/Nekhoroshev/Stability/Transfer.lean)
LEAN_NOTE: audit S7-3 PASS WITH NOTES, proof paragraph at S7-3-audit-1.md:156: uniqueness identifies the two H orbits on their interval intersection.
NOTE: -

NODE: stepN:p7:tr-est
KIND: step
TITLE: Estimate
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:tr-est@L107-L107
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:tr-est@L107-L107
CONTRACT_ID: stepN:p7:tr-est
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (T1), (T3); tr-long, tr-ident
SOURCE_QUANTIFIERS: t in J, |t|<=T(I_y)
SOURCE_CONCLUSION: I(t)-I(0)=(Pi_IPsi(z~(t))-I~(t))+(I~(t)-I~(0))+(I~(0)-I_y) has size <=d_*+rho+d_*
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p7:tr-ident, stepN:p7:tr-long, stepN:p7:tr-orbit
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p7:tr-ident | blueprint-N/parts/p7-stability.tex#stepN:p7:tr-est@L107-L107 | z(t)=Psi(z~(t))
EDGE: stepN:p7:tr-long | blueprint-N/parts/p7-stability.tex#stepN:p7:tr-est@L107-L107 | t in the interval of z~ so (T3) applies
EDGE: stepN:p7:tr-orbit | blueprint-N/parts/p7-stability.tex#stepN:p7:tr-est@L107-L107 | I~(0)=I_x
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7
REVIEWER: sol-review-N-d
LEAN_STATUS: PROVED
LEAN_REF: transfer (KAM/Nekhoroshev/Stability/Transfer.lean)
LEAN_NOTE: audit S7-3 PASS WITH NOTES, proof paragraph at S7-3-audit-1.md:156 (final triangle estimate uses T1 twice and T3 once, giving rho+2d); row transfer exact T1-T3 type and bound rho+2d (S7-3-audit-1.md:48).
NOTE: -

NODE: bpN:p7:stopped-extension
KIND: corollary
TITLE: Stopped form for any extension of the field
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#bpN:p7:stopped-extension@L110-L112
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#bpN:p7:stopped-extension@L113-L116
CONTRACT_ID: bpN:p7:stopped-extension
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: H in O(r,s)^R; |.|_*>=|.| a norm; 0<rho<r; T in (0,inf]; every H-orbit in W_r on every interval J∋0 with I(0) in D satisfies |I(t)-I(0)|_*<=rho for t in J, |t|<=T; F:R^{2n}->R^{2n} any function with F=X_{H^R} on W_r; z:R->R^{2n}, J∋0 an interval with HasDerivAt z (F(z t)) t for all t in J (two-sided, endpoints included) and z(0) in R^n×D
SOURCE_QUANTIFIERS: H; |.|_*; rho; T; F; z; J
SOURCE_CONCLUSION: |I(t)-I(0)|_*<=rho for t in J, |t|<=T; in particular z(t) in W_r there
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p7:se-stop, stepN:p7:se-noexit, bpN:p7:setting, bpN:p4:norm, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p7:se-stop | blueprint-N/parts/p7-stability.tex#bpN:p7:stopped-extension@L114-L114 | proof step
EDGE: stepN:p7:se-noexit | blueprint-N/parts/p7-stability.tex#bpN:p7:stopped-extension@L115-L115 | proof step
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#bpN:p7:stopped-extension@L111-L111 | orbits, W_r, U_r D
EDGE: bpN:p4:norm | blueprint-N/parts/p7-stability.tex#bpN:p7:stopped-extension@L111-L111 | the consumer uses O(r,s), Fourier coefficients or the weighted norm directly
EDGE: bpN:p5:setting | blueprint-N/parts/p7-stability.tex#bpN:p7:stopped-extension@L111-L111 | the consumer uses X_G or the symplectic matrix J directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: stopped_extension (KAM/Nekhoroshev/Stability/Transfer.lean)
LEAN_NOTE: audit S7-3 PASS WITH NOTES
NOTE: -

NODE: stepN:p7:se-stop
KIND: step
TITLE: The stopped interval
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:se-stop@L114-L114
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:se-stop@L114-L114
CONTRACT_ID: stepN:p7:se-stop
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: statement of stopped-extension
SOURCE_QUANTIFIERS: J'
SOURCE_CONCLUSION: {t in J: z(t) in W_r} is relatively open in J (continuity) and contains 0; on its component J' through 0 z is an H-orbit in W_r, so the bound holds on J'∩[-T,T]
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:gen-sol#consequences, bpN:p7:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:gen-sol#consequences | blueprint-N/parts/p7-stability.tex#stepN:p7:se-stop@L114-L114 | continuity of z and restriction of IsSolIn to the subinterval J'
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:se-stop@L114-L114 | W_r, H-orbit in W_r
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7
REVIEWER: sol-review-N-d
LEAN_STATUS: BYPASSED
LEAN_REF: stopped_extension (KAM/Nekhoroshev/Stability/Transfer.lean)
LEAN_NOTE: BYPASSED (D27): Lean stopped_extension (Transfer.lean:86, audit S7-3 PASS WITH NOTES) does not construct the relatively open set {t in J : z(t) in W_r} or its component J'; it argues on each closed initial segment inside the open strip with gen_exit and a closed cylinder C (stay_forward, Transfer:49) (S7-3-audit-1.md:150; note 3 at S7-3-audit-1.md:250). Route taken: stopped_extension.
NOTE: -

NODE: stepN:p7:se-noexit
KIND: step
TITLE: No exit
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:se-noexit@L115-L115
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:se-noexit@L115-L115
CONTRACT_ID: stepN:p7:se-noexit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: se-stop; continuity of z
SOURCE_QUANTIFIERS: t_e endpoint of J'
SOURCE_CONCLUSION: if t_e in J∩[-T,T] were an endpoint of J' not in J', continuity gives |I(t_e)-I(0)|_*<=rho, hence |I(t_e)-I(0)|<r, I(t_e) in U_r D, so t_e in the component: contradiction
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p7:se-stop, bpN:p3:gen-sol#consequences, bpN:p7:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p7:se-stop | blueprint-N/parts/p7-stability.tex#stepN:p7:se-noexit@L115-L115 | the component J' and the bound on it
EDGE: bpN:p3:gen-sol#consequences | blueprint-N/parts/p7-stability.tex#stepN:p7:se-noexit@L115-L115 | continuity of z at t_e
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:se-noexit@L115-L115 | U_r D, W_r
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7
REVIEWER: sol-review-N-d
LEAN_STATUS: BYPASSED
LEAN_REF: stopped_extension (KAM/Nekhoroshev/Stability/Transfer.lean)
LEAN_NOTE: BYPASSED (D27): the component-endpoint contradiction is replaced in Lean stopped_extension (Transfer.lean:86) by the first-exit argument: a first exit t*>0 lies in the closure of the preceding half-open segment, continuity and the closed cylinder C={Nrm(I-I0)<=rho} place its value in C inside W_r (stay_forward, Transfer:49) (S7-3-audit-1.md:150). Route taken: stopped_extension.
NOTE: -

NODE: bpN:p7:exit-ball
KIND: lemma
TITLE: First exit from a norm ball
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#bpN:p7:exit-ball@L118-L120
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#bpN:p7:exit-ball@L121-L123
CONTRACT_ID: bpN:p7:exit-ball
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: |.|_* a norm on R^n; J∋0 an interval; z:J->R^{2n} continuous; I_0=I(0); rho>0; |I(t_1)-I_0|_*>rho for some t_1 in J
SOURCE_QUANTIFIERS: |.|_*; J; z; rho; t_1
SOURCE_CONCLUSION: there is t* in J between 0 and t_1 with |I(t*)-I_0|_*=rho and |I(tau)-I_0|_*<=rho for all tau between 0 and t*
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p7:eb-exit
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p7:eb-exit | blueprint-N/parts/p7-stability.tex#bpN:p7:exit-ball@L122-L122 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7
REVIEWER: sol-review-N-d
LEAN_STATUS: PROVED
LEAN_REF: exit_ball (KAM/Nekhoroshev/Stability/Setting.lean)
LEAN_NOTE: audit S7-1 PASS WITH NOTES
NOTE: -

NODE: stepN:p7:eb-exit
KIND: step
TITLE: Exit set
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:eb-exit@L122-L122
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:eb-exit@L122-L122
CONTRACT_ID: stepN:p7:eb-exit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: statement of exit-ball; V=R^n×{|I-I_0|_*<rho} open, z(0) in V
SOURCE_QUANTIFIERS: t_1
SOURCE_CONCLUSION: Lemma gen-exit (forward for t_1>0, applied to t->z(-t) for t_1<0, only continuity used) gives t* with z(tau) in V before and z(t*) in cl V \ V, i.e. |I(t*)-I_0|_*<=rho and not <rho
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:gen-exit
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:gen-exit | blueprint-N/parts/p7-stability.tex#stepN:p7:eb-exit@L122-L122 | first exit time from the open set V
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7
REVIEWER: sol-review-N-d
LEAN_STATUS: PROVED
LEAN_REF: exit_ball (KAM/Nekhoroshev/Stability/Setting.lean)
LEAN_NOTE: audit S7-1 PASS WITH NOTES, row exit_ball (Setting.lean:220, first boundary hit and closed-ball bound in both time directions, exact statement) at S7-1-audit-1.md:68 and helper first_hit (:186) at S7-1-audit-1.md:75; proved directly rather than through gen_exit, same conclusion.
NOTE: -

NODE: bpN:p7:nonresonant
KIND: proposition
TITLE: Nonresonant stability estimate
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#bpN:p7:nonresonant@L127-L138
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#bpN:p7:nonresonant@L139-L147
CONTRACT_ID: bpN:p7:nonresonant
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n>=1; D subset R^n; r,s,K,alpha>0; L>=0; p>1, q=p/(p-1), kappa=2πKs; h holomorphic on V_rD, real on U_rD; f in O(r,s)^R, eps=|f|_{r,s}<infinity; H=h+f; (i) |k·omega(I)|>=alpha for I in D, k in Z^n with 0<|k|_1<=K; (ii) the Lipschitz bound (N2) for omega with constant L, and KLr<=alpha/p; (iii) eps<=alpha r/(2^7 q K); T_nr=s r e^{kappa/6}/(5 eps) (=infinity if eps=0)
SOURCE_QUANTIFIERS: n; D; r; s; K; alpha; L; p; h; f
SOURCE_CONCLUSION: for every interval J∋0 and every H-orbit z in W_r on J with I(0) in D: |I(t)-I(0)|<=r/2 (<=r) for t in J, |t|<=T_nr
CONSTANT_SCOPE: no convexity is used; the constants depend only on (r,s,K,alpha,p) and on eps
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p7:nr-dataA, stepN:p7:nr-t3, stepN:p7:nr-concA, stepN:p7:nr-caseB, bpN:p7:setting, bpN:p6:setting, bpN:p6#data, bpN:p4:norm, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p7:nr-dataA | blueprint-N/parts/p7-stability.tex#bpN:p7:nonresonant@L141-L141 | proof step
EDGE: stepN:p7:nr-t3 | blueprint-N/parts/p7-stability.tex#bpN:p7:nonresonant@L142-L142 | proof step
EDGE: stepN:p7:nr-concA | blueprint-N/parts/p7-stability.tex#bpN:p7:nonresonant@L145-L145 | proof step
EDGE: stepN:p7:nr-caseB | blueprint-N/parts/p7-stability.tex#bpN:p7:nonresonant@L146-L146 | proof step
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#bpN:p7:nonresonant@L128-L128 | U_rD, W_r, O(r,s)^R, orbits
EDGE: bpN:p6:setting | blueprint-N/parts/p7-stability.tex#bpN:p7:nonresonant@L131-L131 | condition (N2) (cond-L) and (N1) with Lambda={0} in (i)
EDGE: bpN:p6#data | blueprint-N/parts/p7-stability.tex#bpN:p7:nonresonant@L128-L128 | p, q, kappa, Z_K, omega
EDGE: bpN:p4:norm | blueprint-N/parts/p7-stability.tex#bpN:p7:nonresonant@L128-L128 | class O(r,s) and norm ¦f¦_{r,s}
EDGE: bpN:p4:domains | blueprint-N/parts/p7-stability.tex#bpN:p7:nonresonant@L128-L128 | the consumer uses V_rD, D_{r,s} or a strip directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: nonresonant (KAM/Nekhoroshev/Stability/Nonresonant.lean)
LEAN_NOTE: audit S7-7 PASS WITH NOTES
NOTE: dropped candidate edges: Remark p7:factor-e (remark), p6:nonresonant-case at statement level (\source only; consumed in nr-caseB)

NODE: stepN:p7:nr-dataA
KIND: step
TITLE: Case A, $\kappa\ge6$: data
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:nr-dataA@L141-L141
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:nr-dataA@L141-L141
CONTRACT_ID: stepN:p7:nr-dataA
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: kappa>=6; hypotheses (i)-(iii)
SOURCE_QUANTIFIERS: Lambda={0}; Psi
SOURCE_CONCLUSION: Theorem normal-form with Lambda={0} applies ((N1)=(i), (N2) and KLr<=alpha/p=(ii), eps<=alpha r/(2^7 qK)=(iii)); Psi:D_{r/2,s/6}->D_{r,s} holomorphic symplectic real at real points, H∘Psi=h+g+f_*, g theta-independent, f_* in O(r/2,s/6)^R with eta<=e^{-kappa/6}eps, |Pi_IPsi-I|<=d=qK eps/alpha<=r/2^7; data r~=r/2, s~=s/6, rho=15r/32, d_*=d, |.|_*=|.|, T=T_nr; (T1) displacement, (T2) Corollary preimage-nfl; d_*+rho<=61r/128<r~
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p6:normal-form, bpN:p6:setting, bpN:p7:preimage-nfl, bpN:p7:setting, bpN:p6#data, bpN:p4:norm, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p6:normal-form | blueprint-N/parts/p7-stability.tex#stepN:p7:nr-dataA@L141-L141 | Theorem applied with Lambda={0}
EDGE: bpN:p6:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:nr-dataA@L141-L141 | (N1) is (i), (N2) and KLr<=alpha/p are (ii)
EDGE: bpN:p7:preimage-nfl | blueprint-N/parts/p7-stability.tex#stepN:p7:nr-dataA@L141-L141 | (T2)
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:nr-dataA@L141-L141 | real points, f_* in O(r/2,s/6)^R
EDGE: bpN:p6#data | blueprint-N/parts/p7-stability.tex#stepN:p7:nr-dataA@L141-L141 | q, kappa
EDGE: bpN:p4:norm | blueprint-N/parts/p7-stability.tex#stepN:p7:nr-dataA@L141-L141 | eta=¦f_*¦_{r/2,s/6}
EDGE: bpN:p4:domains | blueprint-N/parts/p7-stability.tex#stepN:p7:nr-dataA@L141-L141 | the consumer uses V_rD, D_{r,s} or a strip directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: nonresonant (KAM/Nekhoroshev/Stability/Nonresonant.lean)
LEAN_NOTE: audit S7-7 PASS WITH NOTES, proof items 2-3 (Nonresonant:115-166: normal_form with Lambda={0} on the actual hypotheses (i)-(iii), preimage_nfl giving real preimages and d=qK eps/alpha<=r/128, finite weighted bound for g) at S7-7-audit-1.md:139 and S7-7-audit-1.md:143.
NOTE: -

NODE: stepN:p7:nr-t3
KIND: step
TITLE: Case A: (T3)
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:nr-t3@L142-L144
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:nr-t3@L142-L144
CONTRACT_ID: stepN:p7:nr-t3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: nr-dataA; Lemma exit-ball; theta-derivative bound
SOURCE_QUANTIFIERS: z~ H~-orbit in W_r~, |I~(0)-I_y|<=d, I_y in D
SOURCE_CONCLUSION: (T3) holds with T(I_y)=T_nr: a violation gives t* with |I~(t*)-I~(0)|=rho and I~ in the closed rho-ball B⊂U_r~ D before; |İ~|=|∂_theta f_*(z~)|<=eta/(e s~)=6 eta/(e s); mean value inequality gives rho<=6/(5e) r<0.442 r<15r/32=rho, contradiction
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p7:exit-ball, bpN:p7:real-system, bpN:p7:theta-derivative, K:bp:p1:ext-mvt, bpN:p7:ext-num, stepN:p7:nr-dataA, bpN:p7:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p7:exit-ball | blueprint-N/parts/p7-stability.tex#stepN:p7:nr-t3@L142-L142 | first exit time t*
EDGE: bpN:p7:real-system | blueprint-N/parts/p7-stability.tex#stepN:p7:nr-t3@L142-L142 | (b) İ~=-∂_theta H~^R=-∂_theta f_* (h and g theta-independent)
EDGE: bpN:p7:theta-derivative | blueprint-N/parts/p7-stability.tex#stepN:p7:nr-t3@L142-L142 | ¦∂_theta f_*¦<=eta/(e s~)
EDGE: K:bp:p1:ext-mvt | blueprint-N/parts/p7-stability.tex#stepN:p7:nr-t3@L142-L142 | mean value inequality for I~
EDGE: bpN:p7:ext-num | blueprint-N/parts/p7-stability.tex#stepN:p7:nr-t3@L143-L143 | 6/(5e)<0.442<15/32
EDGE: stepN:p7:nr-dataA | blueprint-N/parts/p7-stability.tex#stepN:p7:nr-t3@L142-L142 | data Psi, g, f_*, eta, rho, d
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:nr-t3@L142-L142 | orbits in W_r~, U_r~ D
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7
REVIEWER: sol-review-N-d
LEAN_STATUS: BYPASSED
LEAN_REF: nonresonant (KAM/Nekhoroshev/Stability/Nonresonant.lean)
LEAN_NOTE: BYPASSED (D27): Lean nonresonant (Nonresonant.lean:92, audit S7-7 PASS WITH NOTES) does not use exit_ball for (T3); it bounds the action drift of the orbit directly by the mean value inequality drift_bound (NonresonantAux:123) with the globally bounded remainder gradient, since gradient bounds are uniform on the full strip (S7-7-audit-1.md:55; route notes at S7-7-audit-1.md:164). Route taken: nonresonant with drift_bound.
NOTE: -

NODE: stepN:p7:nr-concA
KIND: step
TITLE: Case A: conclusion
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:nr-concA@L145-L145
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:nr-concA@L145-L145
CONTRACT_ID: stepN:p7:nr-concA
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: nr-dataA, nr-t3; Lemma transfer
SOURCE_QUANTIFIERS: t in J, |t|<=T_nr
SOURCE_CONCLUSION: Lemma transfer: |I(t)-I(0)|<=15r/32+2r/2^7=31r/64<=r/2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p7:transfer, stepN:p7:nr-dataA, stepN:p7:nr-t3
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p7:transfer | blueprint-N/parts/p7-stability.tex#stepN:p7:nr-concA@L145-L145 | conclusion rho+2d_*
EDGE: stepN:p7:nr-dataA | blueprint-N/parts/p7-stability.tex#stepN:p7:nr-concA@L145-L145 | (T1), (T2), d_*, rho
EDGE: stepN:p7:nr-t3 | blueprint-N/parts/p7-stability.tex#stepN:p7:nr-concA@L145-L145 | (T3)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7
REVIEWER: sol-review-N-d
LEAN_STATUS: PROVED
LEAN_REF: nonresonant (KAM/Nekhoroshev/Stability/Nonresonant.lean)
LEAN_NOTE: audit S7-7 PASS WITH NOTES, proof item 5 (Nonresonant:196-209: transfer with Nrm=||.||, rho=15r/32, d+rho<=61r/128<r/2, bound rho+2d<=31r/64<=r/2) at S7-7-audit-1.md:152.
NOTE: -

NODE: stepN:p7:nr-caseB
KIND: step
TITLE: Case B, $\kappa<6$
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:nr-caseB@L146-L146
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:nr-caseB@L146-L146
CONTRACT_ID: stepN:p7:nr-caseB
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: kappa<6
SOURCE_QUANTIFIERS: Psi=id on D_{r,s}
SOURCE_CONCLUSION: with Psi=id, H~=H, g=0, f_*=f (nonresonant-case), r~=r, s~=s, d_*=0, rho=r/2: (T1),(T2) trivial; (T3) as in nr-t3 with |İ~|<=eps/(e s) and |I~(t*)-I~(0)|<=(eps/(es))·(s r e^{kappa/6}/(5eps))<r/5<r/2 (e^{kappa/6}<e): contradiction; transfer gives |I(t)-I(0)|<=r/2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p6:nonresonant-case, stepN:p7:nr-t3, bpN:p7:exit-ball, bpN:p7:theta-derivative, bpN:p7:real-system, K:bp:p1:ext-mvt, bpN:p7:ext-num, bpN:p7:transfer, bpN:p7:setting, bpN:p4:domains, bpN:p6#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p6:nonresonant-case | blueprint-N/parts/p7-stability.tex#stepN:p7:nr-caseB@L146-L146 | Psi=id, g=0, f_*=f
EDGE: stepN:p7:nr-t3 | blueprint-N/parts/p7-stability.tex#stepN:p7:nr-caseB@L146-L146 | (T3) argument
EDGE: bpN:p7:exit-ball | blueprint-N/parts/p7-stability.tex#stepN:p7:nr-caseB@L146-L146 | first exit time
EDGE: bpN:p7:theta-derivative | blueprint-N/parts/p7-stability.tex#stepN:p7:nr-caseB@L146-L146 | ¦∂_theta f¦<=eps/(es)
EDGE: bpN:p7:real-system | blueprint-N/parts/p7-stability.tex#stepN:p7:nr-caseB@L146-L146 | (b) İ~=-∂_theta f
EDGE: K:bp:p1:ext-mvt | blueprint-N/parts/p7-stability.tex#stepN:p7:nr-caseB@L146-L146 | mean value inequality
EDGE: bpN:p7:ext-num | blueprint-N/parts/p7-stability.tex#stepN:p7:nr-caseB@L146-L146 | numerics e^{kappa/6}<e
EDGE: bpN:p7:transfer | blueprint-N/parts/p7-stability.tex#stepN:p7:nr-caseB@L146-L146 | conclusion
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:nr-caseB@L146-L146 | orbits in W_r, U_r D
EDGE: bpN:p4:domains | blueprint-N/parts/p7-stability.tex#stepN:p7:nr-caseB@L146-L146 | the consumer uses V_rD, D_{r,s} or a strip directly
EDGE: bpN:p6#data | blueprint-N/parts/p7-stability.tex#stepN:p7:nr-caseB@L146-L146 | the consumer uses q, kappa or Z_K directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: BYPASSED
LEAN_REF: nonresonant (KAM/Nekhoroshev/Stability/Nonresonant.lean)
LEAN_NOTE: BYPASSED (D27): for kappa<6 Lean nonresonant (Nonresonant.lean:92, S7-7 PASS WITH NOTES) estimates the drift directly (thetaGradR_h_add, norm_thetaGradR_le, drift_bound, arith_small; Nonresonant:108-114) without manufacturing identity-map transfer data and without nonresonant_case or exit_ball (S7-7-audit-1.md:135; route notes at S7-7-audit-1.md:164). Route taken: nonresonant small-kappa branch.
NOTE: -

NODE: bpN:p7:resonance-data
KIND: definition
TITLE: Resonance data, convexity, quasi-convexity
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#bpN:p7:resonance-data@L155-L159
PROOF_SOURCE: -
CONTRACT_ID: bpN:p7:resonance-data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: D subset R^n; Lambda subset Z^n; Pi=Pi_Lambda; R_Lambda={omega in R^n: k·omega=0 for all k in Lambda}=ker Pi; h as in the setting; U subset U_r D; M>=m with ‖Q(I)‖_{2->2}<=M on U_r D
SOURCE_QUANTIFIERS: D; Lambda; delta; h; U; m; l; M
SOURCE_CONCLUSION: defines: D is delta-close to exact Lambda-resonances if ‖Pi omega(I)‖_2=dist_2(omega(I),R_Lambda)<=delta for all I in D; h is m-convex on U if Q(I)[xi,xi]>=m‖xi‖_2^2 (I in U, xi in R^n); h is l,m-quasi-convex on U if for all I in U, xi: |<omega(I),xi>|>l‖xi‖_2 or Q(I)[xi,xi]>=m‖xi‖_2^2 (equivalently |<omega,xi>|<=l‖xi‖_2 => Q[xi,xi]>=m‖xi‖_2^2; never full positive definiteness); M>=m denotes a Hessian bound (always achievable by enlarging M)
CONSTANT_SCOPE: m<=M, l, delta positive reals as data of the use
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p7:resonant-gradient, bpN:p7:setting, bpN:p7:ext-linalg
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p7:resonant-gradient | blueprint-N/parts/p7-stability.tex#bpN:p7:resonance-data@L156-L156 | Pi=Pi_Lambda notation of Lemma resonant-gradient
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#bpN:p7:resonance-data@L157-L157 | h_R, omega, Q, U_r D
EDGE: bpN:p7:ext-linalg | blueprint-N/parts/p7-stability.tex#bpN:p7:resonance-data@L156-L156 | norm of the orthogonal projection equals distance to its kernel
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: resSpace, IsCloseToRes, IsMConvex, IsQuasiConvex, HessBound (KAM/Nekhoroshev/Stability/Energy.lean)
LEAN_NOTE: audit S7-5 PASS WITH NOTES
NOTE: package for the energy argument (SPEC: bpN:p7:resonance-data)

NODE: bpN:p7:energy-core
KIND: lemma
TITLE: Energy--convexity inequality (reusable core)
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#bpN:p7:energy-core@L161-L171
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#bpN:p7:energy-core@L172-L176
CONTRACT_ID: bpN:p7:energy-core
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U subset R^n open; h_R in C^2(U); g,f in C^1(R^n×U;R); H^R=h_R(I)+g+f on R^n×U; Pi an orthogonal projection of (R^n,‖.‖_2) with Pi^perp ∂_theta g≡0; J∋0 an interval; z with IsSolIn X_{H^R} (R^n×U) J z; t_1 in J; I_0=I(0); Delta I=I(t_1)-I_0; I_s=I_0+s Delta I in U for s in [0,1]; omega_0=∇h_R(I_0)
SOURCE_QUANTIFIERS: U; h_R; g; f; Pi; J; z; t_1
SOURCE_CONCLUSION: (a) h_R(I(t_1))-h_R(I_0)=-[(g+f)(z(t_1))-(g+f)(z(0))]; (b) ‖Pi^perp Delta I‖_2<=|t_1| sup_tau ‖∂_theta f(z(tau))‖_2 (tau between 0 and t_1); (c) h_R(I(t_1))-h_R(I_0)-<omega_0,Delta I>=Q(I_xi)[Delta I,Delta I]/2 for some xi in (0,1); (d) if Q(I_s)[Delta I,Delta I]>=m‖Delta I‖_2^2 for all s in [0,1] then (m/2)‖Delta I‖_2^2<=|(g+f)(z(t_1))-(g+f)(z(0))|+‖Pi omega_0‖_2‖Delta I‖_2+‖omega_0‖_2‖Pi^perp Delta I‖_2
CONSTANT_SCOPE: none; reusable core (no property of h,g,f beyond those stated)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p7:ec-energy, stepN:p7:ec-proj, stepN:p7:ec-taylor, bpN:p3:gen-sol, bpN:p5:setting, bpN:p7:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p7:ec-energy | blueprint-N/parts/p7-stability.tex#bpN:p7:energy-core@L173-L173 | proof step
EDGE: stepN:p7:ec-proj | blueprint-N/parts/p7-stability.tex#bpN:p7:energy-core@L174-L174 | proof step
EDGE: stepN:p7:ec-taylor | blueprint-N/parts/p7-stability.tex#bpN:p7:energy-core@L175-L175 | proof step
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p7-stability.tex#bpN:p7:energy-core@L162-L162 | IsSolIn X_{H^R} (R^n×U) J z
EDGE: bpN:p5:setting | blueprint-N/parts/p7-stability.tex#bpN:p7:energy-core@L162-L162 | X_{H^R}=J∇H^R
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#bpN:p7:energy-core@L162-L162 | h_R, Q, omega, I(t)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7
REVIEWER: sol-review-N-d
LEAN_STATUS: PROVED
LEAN_REF: energy_core (KAM/Nekhoroshev/Stability/Energy.lean)
LEAN_NOTE: audit S7-5 PASS WITH NOTES
NOTE: the reusable core also consumed by track I (energy confinement); it is used inside N-HEAD-C (no-exit) and by Part 11 (bpN:p11:ef-en)

NODE: stepN:p7:ec-energy
KIND: step
TITLE: Energy
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:ec-energy@L173-L173
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:ec-energy@L173-L173
CONTRACT_ID: stepN:p7:ec-energy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: H^R C^1 on the open set R^n×U; z an orbit
SOURCE_QUANTIFIERS: t_1
SOURCE_CONCLUSION: H^R is differentiable along the orbit and ham-energy on the interval between 0 and t_1 gives H^R(z(t_1))=H^R(z(0)); this is (a) since h_R(I(t_1))-h_R(I_0)=H^R(z(t_1))-H^R(z(0))-[(g+f)(z(t_1))-(g+f)(z(0))]
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:ham-energy, bpN:p3:gen-sol, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:ham-energy | blueprint-N/parts/p7-stability.tex#stepN:p7:ec-energy@L173-L173 | conservation of the Hamiltonian along the orbit
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p7-stability.tex#stepN:p7:ec-energy@L173-L173 | z solves X_{H^R} on R^n×U
EDGE: bpN:p5:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:ec-energy@L173-L173 | X_{H^R}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7
REVIEWER: sol-review-N-d
LEAN_STATUS: PROVED
LEAN_REF: energy_core (KAM/Nekhoroshev/Stability/Energy.lean)
LEAN_NOTE: audit S7-5 PASS WITH NOTES, row energy_core (Energy:237) naming steps ec-energy/ec-proj/ec-taylor at S7-5-audit-1.md:39.
NOTE: -

NODE: stepN:p7:ec-proj
KIND: step
TITLE: Resonant projection
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:ec-proj@L174-L174
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:ec-proj@L174-L174
CONTRACT_ID: stepN:p7:ec-proj
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: z orbit; h_R theta-independent; Pi^perp ∂_theta g=0
SOURCE_QUANTIFIERS: t
SOURCE_CONCLUSION: İ=-∂_theta H^R(z)=-∂_theta g-∂_theta f; t->Pi^perp I(t) has derivative -Pi^perp ∂_theta f(z(t)) of norm <=‖∂_theta f(z(t))‖_2; mean value inequality gives (b)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p1:ext-mvt, bpN:p3:gen-sol, bpN:p5:setting, bpN:p7:ext-linalg
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p1:ext-mvt | blueprint-N/parts/p7-stability.tex#stepN:p7:ec-proj@L174-L174 | mean value inequality for t->Pi^perp I(t)
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p7-stability.tex#stepN:p7:ec-proj@L174-L174 | İ is the I-component of X_{H^R}(z)
EDGE: bpN:p5:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:ec-proj@L174-L174 | X_{H^R}=(∂_I H^R,-∂_theta H^R)
EDGE: bpN:p7:ext-linalg | blueprint-N/parts/p7-stability.tex#stepN:p7:ec-proj@L174-L174 | Pi^perp linear, ‖Pi^perp v‖_2<=‖v‖_2
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7
REVIEWER: sol-review-N-d
LEAN_STATUS: PROVED
LEAN_REF: energy_core (KAM/Nekhoroshev/Stability/Energy.lean)
LEAN_NOTE: audit S7-5 PASS WITH NOTES, row energy_core (Energy:237) naming steps ec-energy/ec-proj/ec-taylor at S7-5-audit-1.md:39; conclusion (b) with uniform bound B.
NOTE: -

NODE: stepN:p7:ec-taylor
KIND: step
TITLE: Taylor and combination
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:ec-taylor@L175-L175
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:ec-taylor@L175-L175
CONTRACT_ID: stepN:p7:ec-taylor
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ec-energy (a); phi(s)=h_R(I_s) C^2
SOURCE_QUANTIFIERS: Delta I
SOURCE_CONCLUSION: (c) is Taylor with phi'(0)=<omega_0,Delta I>, phi''=Q(I_s)[Delta I,Delta I]; under the hypothesis of (d), (c) gives (m/2)‖Delta I‖^2<=h_R(I(t_1))-h_R(I_0)-<omega_0,Delta I>; insert (a) and <omega_0,Delta I>=<Pi omega_0,Delta I>+<omega_0,Pi^perp Delta I> with Cauchy-Schwarz
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p7:ext-taylor, bpN:p7:ext-linalg, stepN:p7:ec-energy, bpN:p7:setting, bpN:p1:ext-norms
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p7:ext-taylor | blueprint-N/parts/p7-stability.tex#stepN:p7:ec-taylor@L175-L175 | Lagrange remainder for phi(s)=h_R(I_s)
EDGE: bpN:p7:ext-linalg | blueprint-N/parts/p7-stability.tex#stepN:p7:ec-taylor@L175-L175 | <omega_0,Delta I> split via the orthogonal projection
EDGE: stepN:p7:ec-energy | blueprint-N/parts/p7-stability.tex#stepN:p7:ec-taylor@L175-L175 | (a) inserted into the Taylor expansion
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:ec-taylor@L175-L175 | the consumer uses W_r, U_rD, real Hamiltonians/orbits, omega or Q directly
EDGE: bpN:p1:ext-norms | blueprint-N/parts/p7-stability.tex#stepN:p7:ec-taylor@L175-L175 | Cauchy-Schwarz is used with the orthogonal splitting
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: energy_core (KAM/Nekhoroshev/Stability/Energy.lean)
LEAN_NOTE: audit S7-5 PASS WITH NOTES, row energy_core (Energy:237) naming steps ec-energy/ec-proj/ec-taylor at S7-5-audit-1.md:39; helper taylor_segment (Energy:77); conclusion (c),(d).
NOTE: -

NODE: bpN:p7:admissible
KIND: lemma
TITLE: Admissible initial actions
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#bpN:p7:admissible@L181-L183
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#bpN:p7:admissible@L184-L187
CONTRACT_ID: bpN:p7:admissible
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (RS); I_0 admissible with J_0 in D
SOURCE_QUANTIFIERS: I_0; J_0; I
SOURCE_CONCLUSION: (a) the closed ball B-bar={I:‖I-I_0‖_2<=r-rho}⊂U_rD; (b) ‖Pi omega(I)‖_2<=(5/4)delta+M‖I-I_0‖_2 for I in B-bar, in particular ‖Pi omega(I_0)‖_2<=5delta/4
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p7:ad-ball, stepN:p7:ad-close, bpN:p7:s-energy#rs, bpN:p7:resonance-data, bpN:p7:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p7:ad-ball | blueprint-N/parts/p7-stability.tex#bpN:p7:admissible@L185-L185 | proof step
EDGE: stepN:p7:ad-close | blueprint-N/parts/p7-stability.tex#bpN:p7:admissible@L186-L186 | proof step
EDGE: bpN:p7:s-energy#rs | blueprint-N/parts/p7-stability.tex#bpN:p7:admissible@L182-L182 | (RS) and admissibility
EDGE: bpN:p7:resonance-data | blueprint-N/parts/p7-stability.tex#bpN:p7:admissible@L182-L182 | Pi, delta-closeness
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#bpN:p7:admissible@L182-L182 | U_rD, omega, Q
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7
REVIEWER: sol-review-N-d
LEAN_STATUS: PROVED
LEAN_REF: admissible (KAM/Nekhoroshev/Stability/Resonant.lean)
LEAN_NOTE: audit S7-6 PASS WITH NOTES
NOTE: -

NODE: stepN:p7:ad-ball
KIND: step
TITLE: Ball
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:ad-ball@L185-L185
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:ad-ball@L185-L185
CONTRACT_ID: stepN:p7:ad-ball
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (RS); I_0 admissible
SOURCE_QUANTIFIERS: I in the ball
SOURCE_CONCLUSION: |I-J_0|<=‖I-J_0‖_2<(r-rho)+rho=r so I in U_rD; likewise the segment [J_0,I_0]
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p1:norm-compare, bpN:p7:s-energy#rs, bpN:p7:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p1:norm-compare | blueprint-N/parts/p7-stability.tex#stepN:p7:ad-ball@L185-L185 | ¦x¦<=‖x‖_2
EDGE: bpN:p7:s-energy#rs | blueprint-N/parts/p7-stability.tex#stepN:p7:ad-ball@L185-L185 | rho and admissibility
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:ad-ball@L185-L185 | U_rD=V_rD∩R^n
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7
REVIEWER: sol-review-N-d
LEAN_STATUS: PROVED
LEAN_REF: admissible (KAM/Nekhoroshev/Stability/Resonant.lean)
LEAN_NOTE: audit S7-6 PASS WITH NOTES, row admissible (Resonant:261: closed Euclidean ball inside the open max-norm tube) at S7-6-audit-1.md:42; proof paragraph L261-308 at S7-6-audit-1.md:75.
NOTE: -

NODE: stepN:p7:ad-close
KIND: step
TITLE: Closeness
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:ad-close@L186-L186
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:ad-close@L186-L186
CONTRACT_ID: stepN:p7:ad-close
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ad-ball; D delta-close; mean value inequality for omega in ‖.‖_2 (Domega=Q, ‖Q‖<=M)
SOURCE_QUANTIFIERS: I in B-bar
SOURCE_CONCLUSION: ‖omega(I_0)-omega(J_0)‖_2<=M rho=delta/4, so ‖Pi omega(I_0)‖<=5delta/4, and ‖Pi omega(I)‖<=‖Pi omega(I_0)‖+M‖I-I_0‖_2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p1:ext-mvt, stepN:p7:ad-ball, bpN:p7:resonance-data, bpN:p7:s-energy#rs, bpN:p7:ext-linalg, bpN:p7:setting
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p1:ext-mvt | blueprint-N/parts/p7-stability.tex#stepN:p7:ad-close@L186-L186 | mean value inequality for omega on convex segments in U_rD
EDGE: stepN:p7:ad-ball | blueprint-N/parts/p7-stability.tex#stepN:p7:ad-close@L186-L186 | segments lie in U_rD
EDGE: bpN:p7:resonance-data | blueprint-N/parts/p7-stability.tex#stepN:p7:ad-close@L186-L186 | delta-closeness, Hessian bound M
EDGE: bpN:p7:s-energy#rs | blueprint-N/parts/p7-stability.tex#stepN:p7:ad-close@L186-L186 | rho=delta/(4M)
EDGE: bpN:p7:ext-linalg | blueprint-N/parts/p7-stability.tex#stepN:p7:ad-close@L186-L186 | ‖Pi v‖<=‖v‖, Pi linear
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:ad-close@L186-L186 | omega, Q
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7
REVIEWER: sol-review-N-d
LEAN_STATUS: PROVED
LEAN_REF: admissible (KAM/Nekhoroshev/Stability/Resonant.lean)
LEAN_NOTE: audit S7-6 PASS WITH NOTES, row admissible (projection bound varies by M||I-I0||_2, initial bound 5 delta/4) at S7-6-audit-1.md:42; proof paragraph L261-308 (closeness witness and M rho = delta/4) at S7-6-audit-1.md:75.
NOTE: -

NODE: bpN:p7:no-exit
KIND: lemma
TITLE: No exit under convexity along the segment
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#bpN:p7:no-exit@L189-L198
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#bpN:p7:no-exit@L199-L205
CONTRACT_ID: bpN:p7:no-exit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (RS); z an H-orbit in W_r on J∋0 with I_0=I(0) admissible; t_1 in J\{0} with (i) ‖I(tau)-I_0‖_2<=r-rho for tau between 0 and t_1 and ‖I(t_1)-I_0‖_2=r-rho; (ii) Q(I_s)[Delta I,Delta I]>=m‖Delta I‖_2^2 for s in [0,1] (Delta I=I(t_1)-I_0, I_s=I_0+s Delta I); (iii) |t_1|‖omega(I_0)‖_2 eta<=s m r^2/12
SOURCE_QUANTIFIERS: (RS); z; J; t_1
SOURCE_CONCLUSION: a contradiction arises: (i), (ii), (iii) cannot hold together
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p7:ne-core, stepN:p7:ne-terms, stepN:p7:ne-contra, bpN:p7:s-energy#rs, bpN:p7:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p7:ne-core | blueprint-N/parts/p7-stability.tex#bpN:p7:no-exit@L201-L201 | proof step
EDGE: stepN:p7:ne-terms | blueprint-N/parts/p7-stability.tex#bpN:p7:no-exit@L203-L203 | proof step
EDGE: stepN:p7:ne-contra | blueprint-N/parts/p7-stability.tex#bpN:p7:no-exit@L204-L204 | proof step
EDGE: bpN:p7:s-energy#rs | blueprint-N/parts/p7-stability.tex#bpN:p7:no-exit@L190-L190 | (RS), admissible I_0, rho
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#bpN:p7:no-exit@L190-L190 | orbits in W_r
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7
REVIEWER: sol-review-N-d
LEAN_STATUS: PROVED
LEAN_REF: no_exit (KAM/Nekhoroshev/Stability/Resonant.lean)
LEAN_NOTE: audit S7-6 PASS WITH NOTES
NOTE: -

NODE: stepN:p7:ne-core
KIND: step
TITLE: Apply the core
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:ne-core@L201-L202
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:ne-core@L201-L202
CONTRACT_ID: stepN:p7:ne-core
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (RS); (i), (ii); Delta=‖Delta I‖_2=r-rho>=15r/16
SOURCE_QUANTIFIERS: U=U_rD
SOURCE_CONCLUSION: Lemma energy-core(d) applies (B-bar⊂U convex so I_s in U; g,f_* C^infty on W_r; Pi^perp ∂_theta g=0; the orbit solves X_{H^R} in R^n×U): (m/2)Delta^2<=A+B+C with A=|Delta(g+f_*)|, B=‖Pi omega_0‖Delta, C=‖omega_0‖‖Pi^perp Delta I‖
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p7:admissible, bpN:p7:real-system, bpN:p7:resonant-gradient, bpN:p7:energy-core, bpN:p3:gen-sol#consequences, bpN:p7:s-energy#rs, bpN:p7:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p7:admissible | blueprint-N/parts/p7-stability.tex#stepN:p7:ne-core@L201-L201 | (a) B-bar⊂U_rD
EDGE: bpN:p7:real-system | blueprint-N/parts/p7-stability.tex#stepN:p7:ne-core@L201-L201 | g, f_* C^infty on W_r
EDGE: bpN:p7:resonant-gradient | blueprint-N/parts/p7-stability.tex#stepN:p7:ne-core@L201-L201 | Pi^perp ∂_theta g=0 (P_Lambda g=g)
EDGE: bpN:p7:energy-core | blueprint-N/parts/p7-stability.tex#stepN:p7:ne-core@L201-L201 | (d) with (ii)
EDGE: bpN:p3:gen-sol#consequences | blueprint-N/parts/p7-stability.tex#stepN:p7:ne-core@L201-L201 | restriction of the orbit to a solution in R^n×U
EDGE: bpN:p7:s-energy#rs | blueprint-N/parts/p7-stability.tex#stepN:p7:ne-core@L201-L201 | (RS) data, rho<=r/16
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:ne-core@L201-L201 | orbits in W_r, U_rD
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7
REVIEWER: sol-review-N-d
LEAN_STATUS: PROVED
LEAN_REF: no_exit (KAM/Nekhoroshev/Stability/Resonant.lean)
LEAN_NOTE: audit S7-6 PASS WITH NOTES, row no_exit (Resonant:388) and proof paragraph L310-385 (rs_energy applies energy_core on realNbhd D r with real_system, resonant_gradient, theta_derivative) at S7-6-audit-1.md:43 and S7-6-audit-1.md:78.
NOTE: -

NODE: stepN:p7:ne-terms
KIND: step
TITLE: Three terms
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:ne-terms@L203-L203
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:ne-terms@L203-L203
CONTRACT_ID: stepN:p7:ne-terms
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ne-core; (i), (iii)
SOURCE_QUANTIFIERS: A, B, C
SOURCE_CONCLUSION: A<=2zeta<=mr^2/16; B<=(5/4)delta Delta<=5delta^2/(2m)+mDelta^2/6 with 5delta^2/(2m)<=5mr^2/32 (admissible (b), Young); C<=‖omega_0‖|t_1|eta/(e s)<=mr^2/(12e)<0.0307 mr^2 by (iii)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p7:ne-core, bpN:p7:theta-derivative, bpN:p7:admissible, bpN:p7:energy-core, bpN:p7:ext-num, bpN:p7:s-energy#rs, bpN:p4:norm, bpN:p7:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p7:ne-core | blueprint-N/parts/p7-stability.tex#stepN:p7:ne-terms@L203-L203 | uses A, B, C and Delta from the preceding core step
EDGE: bpN:p7:theta-derivative | blueprint-N/parts/p7-stability.tex#stepN:p7:ne-terms@L203-L203 | ¦u¦<=¦u¦_{r,s} for A and ‖∂_theta f_*‖_2<=eta/(es) for C
EDGE: bpN:p7:admissible | blueprint-N/parts/p7-stability.tex#stepN:p7:ne-terms@L203-L203 | (b) ‖Pi omega_0‖<=5delta/4
EDGE: bpN:p7:energy-core | blueprint-N/parts/p7-stability.tex#stepN:p7:ne-terms@L203-L203 | (b) ‖Pi^perp Delta I‖<=¦t_1¦ sup‖∂_theta f_*‖
EDGE: bpN:p7:ext-num | blueprint-N/parts/p7-stability.tex#stepN:p7:ne-terms@L203-L203 | Young, e>2.7
EDGE: bpN:p7:s-energy#rs | blueprint-N/parts/p7-stability.tex#stepN:p7:ne-terms@L203-L203 | zeta<=mr^2/32, delta<=mr/4
EDGE: bpN:p4:norm | blueprint-N/parts/p7-stability.tex#stepN:p7:ne-terms@L203-L203 | the consumer uses O(r,s), Fourier coefficients or the weighted norm directly
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:ne-terms@L203-L203 | the consumer uses W_r, U_rD, real Hamiltonians/orbits, omega or Q directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: BYPASSED
LEAN_REF: no_exit (KAM/Nekhoroshev/Stability/Resonant.lean)
LEAN_NOTE: BYPASSED (D27): Lean no_exit (Resonant.lean:388, audit S7-6 PASS WITH NOTES) bounds the three terms by A<=mr^2/16, B<=5mr^2/16, C<=mr^2/24 (only exp 1>=2) instead of the blueprint's Young-inequality split of B; the audit states 'This replaces the blueprint's Young-inequality arithmetic without changing its result' (S7-6-audit-1.md:82). Route taken: no_exit.
NOTE: -

NODE: stepN:p7:ne-contra
KIND: step
TITLE: Contradiction
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:ne-contra@L204-L204
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:ne-contra@L204-L204
CONTRACT_ID: stepN:p7:ne-contra
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ne-terms
SOURCE_QUANTIFIERS: Delta
SOURCE_CONCLUSION: (m/3)Delta^2<=mr^2(1/16+5/32+1/(12e))<mr^2/4 while (m/3)Delta^2>=(m/3)(225/256)r^2>0.29 mr^2: contradiction
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p7:ne-terms, stepN:p7:ne-core, bpN:p7:ext-num, bpN:p7:s-energy#rs
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p7:ne-terms | blueprint-N/parts/p7-stability.tex#stepN:p7:ne-contra@L204-L204 | the three bounds
EDGE: stepN:p7:ne-core | blueprint-N/parts/p7-stability.tex#stepN:p7:ne-contra@L204-L204 | (m/2)Delta^2<=A+B+C
EDGE: bpN:p7:ext-num | blueprint-N/parts/p7-stability.tex#stepN:p7:ne-contra@L204-L204 | numerics e>2.7
EDGE: bpN:p7:s-energy#rs | blueprint-N/parts/p7-stability.tex#stepN:p7:ne-contra@L204-L204 | rho<=r/16 gives Delta>=15r/16
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7
REVIEWER: sol-review-N-d
LEAN_STATUS: BYPASSED
LEAN_REF: no_exit (KAM/Nekhoroshev/Stability/Resonant.lean)
LEAN_NOTE: BYPASSED (D27): Lean no_exit (Resonant.lean:388) derives the contradiction as 225 m r^2/512 <= 5 m r^2/12 from its own term bounds, not the blueprint's m/3 Delta^2 <= m r^2/4 versus 0.29 m r^2 (S7-6-audit-1.md:82). Route taken: no_exit.
NOTE: -

NODE: bpN:p7:resonant-lemma2
KIND: lemma
TITLE: Lemma 2: stability for $\ell,m$-quasi-convex $h$ in normal form
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#bpN:p7:resonant-lemma2@L220-L226
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#bpN:p7:resonant-lemma2@L227-L233
CONTRACT_ID: bpN:p7:resonant-lemma2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (RS) with h l,m-quasi-convex on U_rD; (R) r<=2l/m and Mr<=l/4 (the second is an added hypothesis); I_0 admissible; Omega=max{‖omega(I)‖_2: ‖I-I_0‖_2<=r-rho}; z an H-orbit in W_r on J∋0 with I(0)=I_0
SOURCE_QUANTIFIERS: (RS); l; I_0; z; J
SOURCE_CONCLUSION: ‖I(t)-I_0‖_2<=r-rho for t in J, |t|<=T_*, T_*=s m r^2/(12 Omega eta) (=infinity if Omega eta=0)
CONSTANT_SCOPE: Omega depends on I_0 and r; T_* depends on I_0 through Omega
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p7:l2-exit, stepN:p7:l2-iii, stepN:p7:l2-cone, stepN:p7:l2-conv, bpN:p7:s-energy#rs, bpN:p7:resonance-data, bpN:p7:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p7:l2-exit | blueprint-N/parts/p7-stability.tex#bpN:p7:resonant-lemma2@L228-L228 | proof step
EDGE: stepN:p7:l2-iii | blueprint-N/parts/p7-stability.tex#bpN:p7:resonant-lemma2@L229-L229 | proof step
EDGE: stepN:p7:l2-cone | blueprint-N/parts/p7-stability.tex#bpN:p7:resonant-lemma2@L230-L230 | proof step
EDGE: stepN:p7:l2-conv | blueprint-N/parts/p7-stability.tex#bpN:p7:resonant-lemma2@L232-L232 | proof step
EDGE: bpN:p7:s-energy#rs | blueprint-N/parts/p7-stability.tex#bpN:p7:resonant-lemma2@L221-L221 | (RS), admissibility, rho, eta
EDGE: bpN:p7:resonance-data | blueprint-N/parts/p7-stability.tex#bpN:p7:resonant-lemma2@L221-L221 | l,m-quasi-convexity on U_rD
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#bpN:p7:resonant-lemma2@L221-L221 | orbits in W_r, omega
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7
REVIEWER: sol-review-N-d
LEAN_STATUS: PROVED
LEAN_REF: resonant_lemma2 (KAM/Nekhoroshev/Stability/Resonant.lean)
LEAN_NOTE: audit S7-6 PASS WITH NOTES
NOTE: dropped candidate edge: Remark p7:errata (administrative; the added hypothesis Mr<=l/4 is stated in (R))

NODE: stepN:p7:l2-exit
KIND: step
TITLE: Exit
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:l2-exit@L228-L228
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:l2-exit@L228-L228
CONTRACT_ID: stepN:p7:l2-exit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (RS); violation of the claim
SOURCE_QUANTIFIERS: t*
SOURCE_CONCLUSION: a violation yields t*, |t*|<=T_* with (i) of no-exit; Delta=r-rho>=15r/16; I_s in B-bar and ‖omega(I_s)‖<=Omega
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p7:exit-ball, bpN:p7:admissible, bpN:p7:s-energy#rs, bpN:p7:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p7:exit-ball | blueprint-N/parts/p7-stability.tex#stepN:p7:l2-exit@L228-L228 | first exit time with ¦.¦_*=‖.‖_2
EDGE: bpN:p7:admissible | blueprint-N/parts/p7-stability.tex#stepN:p7:l2-exit@L228-L228 | B-bar⊂U_rD convex, so I_s in B-bar
EDGE: bpN:p7:s-energy#rs | blueprint-N/parts/p7-stability.tex#stepN:p7:l2-exit@L228-L228 | rho<=r/16
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:l2-exit@L228-L228 | the consumer uses W_r, U_rD, real Hamiltonians/orbits, omega or Q directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: resonant_lemma2 (KAM/Nekhoroshev/Stability/Resonant.lean)
LEAN_NOTE: audit S7-6 PASS WITH NOTES, row resonant_lemma2 (Resonant:447) at S7-6-audit-1.md:45 and proof paragraphs L413-444 (exit_ball gives actual first boundary time) and L447-514 at S7-6-audit-1.md:86.
NOTE: -

NODE: stepN:p7:l2-iii
KIND: step
TITLE: (iii)
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:l2-iii@L229-L229
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:l2-iii@L229-L229
CONTRACT_ID: stepN:p7:l2-iii
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: l2-exit
SOURCE_QUANTIFIERS: t*
SOURCE_CONCLUSION: ‖omega(I_0)‖<=Omega, so |t*|‖omega(I_0)‖eta<=|t*|Omega eta<=s m r^2/12: (iii) of no-exit
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p7:l2-exit, bpN:p7:s-energy#rs, bpN:p7:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p7:l2-exit | blueprint-N/parts/p7-stability.tex#stepN:p7:l2-iii@L229-L229 | t*, ¦t*¦<=T_*
EDGE: bpN:p7:s-energy#rs | blueprint-N/parts/p7-stability.tex#stepN:p7:l2-iii@L229-L229 | eta
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:l2-iii@L229-L229 | the consumer uses W_r, U_rD, real Hamiltonians/orbits, omega or Q directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: resonant_lemma2 (KAM/Nekhoroshev/Stability/Resonant.lean)
LEAN_NOTE: audit S7-6 PASS WITH NOTES, row resonant_lemma2 (arbitrary valid Omega bound) at S7-6-audit-1.md:45; proof paragraph L447-514 ('Omega bounds every chord frequency ... time bound give the error <= m r^2/24') at S7-6-audit-1.md:89.
NOTE: -

NODE: stepN:p7:l2-cone
KIND: step
TITLE: The cone condition along the segment
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:l2-cone@L230-L231
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:l2-cone@L230-L231
CONTRACT_ID: stepN:p7:l2-cone
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: l2-exit, l2-iii; (R)
SOURCE_QUANTIFIERS: s' in [0,1]
SOURCE_CONCLUSION: |<omega(I_{s'}),Delta I>|<=‖Pi omega(I_{s'})‖Delta+‖omega(I_{s'})‖‖Pi^perp Delta I‖<(0.3453·2l+l/4)Delta<0.941 l‖Delta I‖_2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p7:admissible, bpN:p7:energy-core, bpN:p7:theta-derivative, stepN:p7:l2-iii, stepN:p7:l2-exit, bpN:p7:ext-num, bpN:p7:s-energy#rs, bpN:p7:setting, bpN:p7:resonance-data, bpN:p7:ext-linalg, bpN:p1:ext-norms
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p7:admissible | blueprint-N/parts/p7-stability.tex#stepN:p7:l2-cone@L230-L230 | (b) ‖Pi omega(I_{s'})‖<=5delta/4+Mr
EDGE: bpN:p7:energy-core | blueprint-N/parts/p7-stability.tex#stepN:p7:l2-cone@L230-L230 | (b) ‖Pi^perp Delta I‖<=¦t*¦ sup‖∂_theta f_*‖
EDGE: bpN:p7:theta-derivative | blueprint-N/parts/p7-stability.tex#stepN:p7:l2-cone@L230-L230 | ‖∂_theta f_*‖<=eta/(es)
EDGE: stepN:p7:l2-iii | blueprint-N/parts/p7-stability.tex#stepN:p7:l2-cone@L230-L230 | ¦t*¦Omega eta<=s m r^2/12
EDGE: stepN:p7:l2-exit | blueprint-N/parts/p7-stability.tex#stepN:p7:l2-cone@L230-L230 | Delta, I_{s'}, t*
EDGE: bpN:p7:ext-num | blueprint-N/parts/p7-stability.tex#stepN:p7:l2-cone@L230-L230 | 1/(12e) numerics
EDGE: bpN:p7:s-energy#rs | blueprint-N/parts/p7-stability.tex#stepN:p7:l2-cone@L230-L230 | delta<=mr/4
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:l2-cone@L230-L230 | the consumer uses W_r, U_rD, real Hamiltonians/orbits, omega or Q directly
EDGE: bpN:p7:resonance-data | blueprint-N/parts/p7-stability.tex#stepN:p7:l2-cone@L230-L230 | the projection/resonance or quasi-convexity definition is used directly
EDGE: bpN:p7:ext-linalg | blueprint-N/parts/p7-stability.tex#stepN:p7:l2-cone@L230-L230 | self-adjoint orthogonal splitting of the inner product
EDGE: bpN:p1:ext-norms | blueprint-N/parts/p7-stability.tex#stepN:p7:l2-cone@L230-L230 | Cauchy-Schwarz is used with the orthogonal splitting
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: BYPASSED
LEAN_REF: resonant_lemma2 (KAM/Nekhoroshev/Stability/Resonant.lean)
LEAN_NOTE: BYPASSED (D27): Lean resonant_lemma2 (Resonant.lean:447, audit S7-6 PASS WITH NOTES) proves the cone condition with its own numerics: projection term <=(7/8) l Delta, using mr<=2l and r<=(16/15)Delta, total (7/8+4/45) l Delta = 347/360 l Delta <= l Delta, not the blueprint's 0.941 l ||Delta I|| (S7-6-audit-1.md:89; 'weaker numerical estimates ... remain sufficient' S7-6-audit-1.md:95). Route taken: resonant_lemma2.
NOTE: -

NODE: stepN:p7:l2-conv
KIND: step
TITLE: Convexity along the segment
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:l2-conv@L232-L232
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:l2-conv@L232-L232
CONTRACT_ID: stepN:p7:l2-conv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: l2-cone
SOURCE_QUANTIFIERS: s'
SOURCE_CONCLUSION: since |<omega(I_{s'}),Delta I>|<=l‖Delta I‖_2 the first alternative of quasi-convexity fails, so Q(I_{s'})[Delta I,Delta I]>=m‖Delta I‖^2: (ii) of no-exit holds and no-exit gives the contradiction
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p7:l2-cone, bpN:p7:resonance-data, bpN:p7:no-exit, stepN:p7:l2-exit, stepN:p7:l2-iii, bpN:p7:s-energy#rs, bpN:p7:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p7:l2-cone | blueprint-N/parts/p7-stability.tex#stepN:p7:l2-conv@L232-L232 | cone condition along the segment
EDGE: bpN:p7:resonance-data | blueprint-N/parts/p7-stability.tex#stepN:p7:l2-conv@L232-L232 | definition of l,m-quasi-convexity
EDGE: bpN:p7:no-exit | blueprint-N/parts/p7-stability.tex#stepN:p7:l2-conv@L232-L232 | (i)-(iii) cannot hold together
EDGE: stepN:p7:l2-exit | blueprint-N/parts/p7-stability.tex#stepN:p7:l2-conv@L232-L232 | (i) and the segment I_{s'}
EDGE: stepN:p7:l2-iii | blueprint-N/parts/p7-stability.tex#stepN:p7:l2-conv@L232-L232 | (iii)
EDGE: bpN:p7:s-energy#rs | blueprint-N/parts/p7-stability.tex#stepN:p7:l2-conv@L232-L232 | the no-exit application uses RS, its admissibility and rho
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:l2-conv@L232-L232 | the consumer uses W_r, U_rD, real Hamiltonians/orbits, omega or Q directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: resonant_lemma2 (KAM/Nekhoroshev/Stability/Resonant.lean)
LEAN_NOTE: audit S7-6 PASS WITH NOTES, proof paragraph L447-514 at S7-6-audit-1.md:89: the cone inequality contradicts the strict first quasi-convex alternative, leaving the Hessian lower bound required by no_exit; row resonant_lemma2 (S7-6-audit-1.md:45).
NOTE: -

NODE: bpN:p7:resonant-prop2
KIND: proposition
TITLE: Resonant Stability Lemma
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#bpN:p7:resonant-prop2@L237-L252
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#bpN:p7:resonant-prop2@L253-L262
CONTRACT_ID: bpN:p7:resonant-prop2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n>=1; D subset R^n; r,s,K,alpha>0; 1<p<=3/2, q=p/(p-1)>=3, kappa=2πKs; Lambda subset Z^n a subgroup; 0<m<=M; l,delta>0; h holomorphic on V_rD and real on U_rD with ‖∂_I^2 h(I)‖_{2->2}<=M for all I in V_rD (complex Hessian), h l,m-quasi-convex on U_rD; f in O(r,s)^R with eps=|f|_{r,s}<infinity; H=h+f; (a) |k·omega(I)|>=alpha for I in D, k in Z_K\Lambda, and D delta-close to exact Lambda-resonances; (b) eps<=(p/q)(m r^2/2^7) and delta<=mr/8; (c) r<=min(alpha/(p sqrt(n) M K), 4l/m) and (added) Mr<=l/2
SOURCE_QUANTIFIERS: n; D; r; s; K; alpha; p; Lambda; m; M; l; delta; h; f; then I_0, J, z
SOURCE_CONCLUSION: for every interval J∋0 and every H-orbit z in W_r on J with I_0=I(0) in D: ‖I(t)-I_0‖_2<=r/2 (so |I(t)-I_0|<=r) for t in J, |t|<=T(I_0)=s m r^2 e^{kappa/6}/(288 Omega(I_0) eps), Omega(I_0)=max{‖omega(I)‖_2:‖I-I_0‖_2<=r/2} (=infinity if Omega eps=0); and for Lambda=Z^n this holds for all t in J
CONSTANT_SCOPE: Omega(I_0) is the maximum of the Euclidean frequency norm on the closed radius-r/2 ball about I_0; T(I_0)=s m r^2 exp(kappa/6)/(288 Omega(I_0) eps), with the stated infinity convention. The source states no additional uniform dependence claim.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p7:p2-red, stepN:p7:p2-cases, stepN:p7:p2-t12, stepN:p7:p2-t3, stepN:p7:p2-concl, bpN:p7:setting, bpN:p7:resonance-data, bpN:p6#data, bpN:p4:norm, bpN:p6:setting, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p7:p2-red | blueprint-N/parts/p7-stability.tex#bpN:p7:resonant-prop2@L254-L254 | proof step
EDGE: stepN:p7:p2-cases | blueprint-N/parts/p7-stability.tex#bpN:p7:resonant-prop2@L255-L255 | proof step
EDGE: stepN:p7:p2-t12 | blueprint-N/parts/p7-stability.tex#bpN:p7:resonant-prop2@L259-L259 | proof step
EDGE: stepN:p7:p2-t3 | blueprint-N/parts/p7-stability.tex#bpN:p7:resonant-prop2@L260-L260 | proof step
EDGE: stepN:p7:p2-concl | blueprint-N/parts/p7-stability.tex#bpN:p7:resonant-prop2@L261-L261 | proof step
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#bpN:p7:resonant-prop2@L238-L240 | U_rD, W_r, O(r,s)^R, orbits
EDGE: bpN:p7:resonance-data | blueprint-N/parts/p7-stability.tex#bpN:p7:resonant-prop2@L238-L242 | delta-closeness, l,m-quasi-convexity, Hessian bound M
EDGE: bpN:p6#data | blueprint-N/parts/p7-stability.tex#bpN:p7:resonant-prop2@L238-L238 | p, q, kappa, Z_K
EDGE: bpN:p4:norm | blueprint-N/parts/p7-stability.tex#bpN:p7:resonant-prop2@L240-L240 | class O(r,s) and norm
EDGE: bpN:p6:setting | blueprint-N/parts/p7-stability.tex#bpN:p7:resonant-prop2@L242-L242 | the consumer assumes/uses the Part-6 resonant setting or nonresonance
EDGE: bpN:p4:domains | blueprint-N/parts/p7-stability.tex#bpN:p7:resonant-prop2@L239-L239 | the complex Hessian is bounded on V_rD
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: resonant_prop2 (KAM/Nekhoroshev/Stability/ResonantStability.lean)
LEAN_NOTE: audit S7-8 PASS WITH NOTES
NOTE: dropped candidate edge: Remark p7:errata (administrative); the added hypothesis Mr<=l/2 is part of (c)

NODE: stepN:p7:p2-red
KIND: step
TITLE: Reductions
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:p2-red@L254-L254
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:p2-red@L254-L254
CONTRACT_ID: stepN:p7:p2-red
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: statement of prop2; (a)-(c)
SOURCE_QUANTIFIERS: delta'=mr/8; L=sqrt(n)M
SOURCE_CONCLUSION: delta'=mr/8>=delta, rho'=mr/(32M); eps<=mr^2/2^8 (p/q<=1/2); L:=sqrt(n)M satisfies KLr<=alpha/p and eps<=alpha r/(2^7 qK); the complex Hessian bound gives (N2) with L=sqrt(n)M (|Qv|_inf<=‖Qv‖_2<=M‖v‖_2<=sqrt(n)M|v|_inf); r~=r/2 with M r~<=l/4, r~<=2l/m, delta'=m r~/4
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p6:setting, bpN:p6:lipschitz, bpN:p1:norm-compare, bpN:p7:resonance-data, bpN:p6#data, bpN:p7:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p6:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-red@L254-L254 | (N2) cond-L with L=sqrt(n)M and KLr<=alpha/p
EDGE: bpN:p6:lipschitz | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-red@L254-L254 | Hessian operator-norm bound gives (N2)
EDGE: bpN:p1:norm-compare | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-red@L254-L254 | ¦x¦_inf<=‖x‖_2<=sqrt(n)¦x¦_inf
EDGE: bpN:p7:resonance-data | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-red@L254-L254 | delta-closeness (monotone in delta), Hessian bound M
EDGE: bpN:p6#data | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-red@L254-L254 | p, q, K
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-red@L254-L254 | the consumer uses W_r, U_rD, real Hamiltonians/orbits, omega or Q directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: resonant_prop2 (KAM/Nekhoroshev/Stability/ResonantStability.lean)
LEAN_NOTE: audit S7-8 PASS WITH NOTES, rows labelled p2-red (realInclusion_mem_polyNbhd'', euclid_ofReal', norm_apply_le_euclid, contDiffOn_realPart, fderiv_realPart, hessBound_of_complex, freqLipschitz_of_complex, Prop2Hyp.nums) at S7-8-audit-1.md:81 to S7-8-audit-1.md:56.
NOTE: -

NODE: stepN:p7:p2-cases
KIND: step
TITLE: Three cases
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:p2-cases@L255-L258
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:p2-cases@L255-L258
CONTRACT_ID: stepN:p7:p2-cases
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: p2-red; (a)-(c)
SOURCE_QUANTIFIERS: three cases
SOURCE_CONCLUSION: (A) Lambda≠Z^n, kappa>=6: normal-form gives Psi, H∘Psi=h+g+f_*, P_Lambda g=g, eta<=e^{-kappa/6}eps, |g|_{r/2,s/6}+eta<=(5/4)eps+eps/e<2eps=:zeta; (B) Lambda≠Z^n, kappa<6: Psi=id on D_{r/2,s}, g=0, f_*=f, zeta=eps; (C) Lambda=Z^n: Psi=id, g=f, f_*=0, eta=0, zeta=eps; in all cases H~=h+g+f_* is in (RS) with (r,s)->(r~,s~), delta'=m r~/4, zeta<=2eps<=m r~^2/32
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p6:normal-form, bpN:p6:setting, stepN:p7:p2-red, bpN:p7:s-energy#rs, bpN:p4:projections, bpN:p6#data, bpN:p4:norm, bpN:p7:ext-num, bpN:p7:setting, bpN:p4:domains, bpN:p4:norm#monotone
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p6:normal-form | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-cases@L255-L255 | Theorem applied in case A (conditions (N1), (N2), K>0, (i), (ii); reality)
EDGE: bpN:p6:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-cases@L255-L255 | (N1), (N2), KLr<=alpha/p
EDGE: stepN:p7:p2-red | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-cases@L255-L255 | L=sqrt(n)M, eps<=alpha r/(2^7 qK), r~, delta'
EDGE: bpN:p7:s-energy#rs | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-cases@L258-L258 | H~ is in (RS) with the new data
EDGE: bpN:p4:projections | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-cases@L255-L257 | case A uses ¦g_0¦<=eps for g_0=P_Lambda T_K f; case C uses P_Lambda f=f
EDGE: bpN:p6#data | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-cases@L255-L255 | kappa, q, c=2qK/(alpha r)
EDGE: bpN:p4:norm | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-cases@L255-L255 | norm bound for g and f_*
EDGE: bpN:p7:ext-num | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-cases@L255-L255 | e>2: 5/4+1/e<2
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-cases@L255-L255 | the consumer uses W_r, U_rD, real Hamiltonians/orbits, omega or Q directly
EDGE: bpN:p4:domains | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-cases@L255-L255 | the consumer uses V_rD, D_{r,s} or a strip directly
EDGE: bpN:p4:norm#monotone | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-cases@L256-L257 | the original f is restricted to the half-radius domain in cases B/C
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: resonant_prop2 (KAM/Nekhoroshev/Stability/ResonantStability.lean)
LEAN_NOTE: audit S7-8 PASS WITH NOTES, rows p2-cases A/B/C: prop2_idData, prop2_caseC (R:195), prop2_caseB (R:220), prop2_caseA (R:256) at S7-8-audit-1.md:98 to S7-8-audit-1.md:102; resonant_prop2 (R:369) S7-8-audit-1.md:103.
NOTE: -

NODE: stepN:p7:p2-t12
KIND: step
TITLE: (T1), (T2)
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:p2-t12@L259-L259
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:p2-t12@L259-L259
CONTRACT_ID: stepN:p7:p2-t12
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: p2-cases; Theorem normal-form (c)
SOURCE_QUANTIFIERS: (T1), (T2); |.|_*=‖.‖_2; rho=r~-rho'
SOURCE_CONCLUSION: case A: ‖Pi_IPsi-I‖_2<=sqrt(n) qK eps/alpha<=q eps/(p M r)<=mr/(2^7 M)=rho'/4=:d_* (normal-form (c), alpha>=p sqrt(n) M K r, (b)); (T2) is Corollary preimage-nfl; cases B, C: d_*=0 trivial; d_*+rho<r~
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p6:normal-form, bpN:p7:preimage-nfl, bpN:p1:norm-compare, stepN:p7:p2-red, stepN:p7:p2-cases, bpN:p6#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p6:normal-form | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-t12@L259-L259 | (c) displacement bound ¦Pi_IPsi-I¦_inf<=qK eps/alpha
EDGE: bpN:p7:preimage-nfl | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-t12@L259-L259 | (T2) in case A
EDGE: bpN:p1:norm-compare | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-t12@L259-L259 | ‖.‖_2<=sqrt(n)¦.¦_inf
EDGE: stepN:p7:p2-red | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-t12@L259-L259 | rho'=mr/(32M)
EDGE: stepN:p7:p2-cases | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-t12@L259-L259 | cases A, B, C
EDGE: bpN:p6#data | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-t12@L259-L259 | q
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7
REVIEWER: sol-review-N-d
LEAN_STATUS: PROVED
LEAN_REF: resonant_prop2 (KAM/Nekhoroshev/Stability/ResonantStability.lean)
LEAN_NOTE: audit S7-8 PASS WITH NOTES, rows p2-t12/t3/concl prop2_core (C:33) and p2-cases A / p2-t12 prop2_caseA (R:256), reMap_eq_of, euclid_re_le, mem_realStrip_of_mem at S7-8-audit-1.md:88 and S7-8-audit-1.md:102.
NOTE: -

NODE: stepN:p7:p2-t3
KIND: step
TITLE: (T3)
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:p2-t3@L260-L260
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:p2-t3@L260-L260
CONTRACT_ID: stepN:p7:p2-t3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n>=1; D subset R^n; r,s,K,alpha>0; 1<p<=3/2, q=p/(p-1)>=3, kappa=2πKs; Lambda subset Z^n a subgroup; 0<m<=M; l,delta>0; h holomorphic on V_rD and real on U_rD with ‖∂_I^2 h(I)‖_{2->2}<=M for all I in V_rD (complex Hessian), h l,m-quasi-convex on U_rD; f in O(r,s)^R with eps=|f|_{r,s}<infinity; H=h+f; (a) |k·omega(I)|>=alpha for I in D, k in Z_K\Lambda, and D delta-close to exact Lambda-resonances; (b) eps<=(p/q)(m r^2/2^7) and delta<=mr/8; (c) r<=min(alpha/(p sqrt(n) M K), 4l/m) and (added) Mr<=l/2; local T3 input: z~ is an H~-orbit in W_r~ on an interval J containing 0, with I_y in D and Euclidean norm of I~(0)-I_y at most d_*<rho'; r~,s~,H~,eta,rho',d_* denote the objects constructed at p2-red, p2-cases and p2-t12, whose established conclusions are dependencies rather than extra assumptions
SOURCE_QUANTIFIERS: z~ H~-orbit in W_r~, ‖I~(0)-I_y‖_2<=d_*<rho', I_y in D
SOURCE_CONCLUSION: I~(0) is admissible; Lemma 2 (R) at radius r~ gives ‖I~(t)-I~(0)‖_2<=rho=r~-rho' for |t|<=T~_*=(s~ m r~^2)/(12 Omega~ eta); the rho-ball lies in {‖I-I_y‖<=r/2} so Omega~<=Omega(I_y); case A: T~_*>=T(I_y); case B: T~_*>=T(I_y) since e^{kappa/6}<e<6; case C: T~_*=infinity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p7:resonant-lemma2, bpN:p7:s-energy#rs, stepN:p7:p2-red, stepN:p7:p2-cases, stepN:p7:p2-t12, bpN:p7:setting, bpN:p7:resonance-data, bpN:p6#data, bpN:p6:ext-numerics, bpN:p4:norm, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p7:resonant-lemma2 | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-t3@L260-L260 | stability in normal-form coordinates
EDGE: bpN:p7:s-energy#rs | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-t3@L260-L260 | admissibility of I~(0) in (RS)
EDGE: stepN:p7:p2-red | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-t3@L260-L260 | rho', r~, (R) at radius r~
EDGE: stepN:p7:p2-cases | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-t3@L260-L260 | H~, eta, s~ in the three cases
EDGE: stepN:p7:p2-t12 | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-t3@L260-L260 | d_*, rho
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-t3@L260-L260 | the consumer uses W_r, U_rD, real Hamiltonians/orbits, omega or Q directly
EDGE: bpN:p7:resonance-data | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-t3@L260-L260 | the projection/resonance or quasi-convexity definition is used directly
EDGE: bpN:p6#data | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-t3@L260-L260 | the consumer uses q, kappa or Z_K directly
EDGE: bpN:p6:ext-numerics | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-t3@L260-L260 | the upper bound e<6 follows from the listed e^2<8; Part-7 numerics only gives a lower bound for e
EDGE: bpN:p4:norm | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-t3@L260-L260 | epsilon and eta are the weighted norms of f and the constructed f_*, used in the time comparison
EDGE: bpN:p4:domains | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-t3@L260-L260 | inherited h and f domain premises on V_rD and D_{r,s}, and their normal-form restrictions
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7+sol-delta2-N-d
REVIEWER: sol-delta3-N-a
LEAN_STATUS: PROVED
LEAN_REF: resonant_prop2 (KAM/Nekhoroshev/Stability/ResonantStability.lean)
LEAN_NOTE: audit S7-8 PASS WITH NOTES, rows p2-t12/t3/concl prop2_core (C:33, transfer helper discharged by cases) at S7-8-audit-1.md:88; case arithmetic at S7-8-audit-1.md:69.
NOTE: -

NODE: stepN:p7:p2-concl
KIND: step
TITLE: Conclusion
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:p2-concl@L261-L261
PROOF_SOURCE: blueprint-N/parts/p7-stability.tex#stepN:p7:p2-concl@L261-L261
CONTRACT_ID: stepN:p7:p2-concl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: p2-t3, p2-t12; Lemma transfer
SOURCE_QUANTIFIERS: t in J, |t|<=T(I_0)
SOURCE_CONCLUSION: Lemma transfer: ‖I(t)-I_0‖_2<=rho+2d_*<=r~-rho'+rho'/2<r/2 for |t|<=T(I_0), all t in case C; and |.|<=‖.‖_2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p7:transfer, stepN:p7:p2-t3, stepN:p7:p2-t12, stepN:p7:p2-cases, bpN:p1:norm-compare, bpN:p7:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p7:transfer | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-concl@L261-L261 | conclusion rho+2d_* in the norm ‖.‖_2
EDGE: stepN:p7:p2-t3 | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-concl@L261-L261 | (T3)
EDGE: stepN:p7:p2-t12 | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-concl@L261-L261 | (T1), (T2), d_*, rho
EDGE: stepN:p7:p2-cases | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-concl@L261-L261 | case C: all t
EDGE: bpN:p1:norm-compare | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-concl@L261-L261 | ¦x¦<=‖x‖_2
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#stepN:p7:p2-concl@L261-L261 | orbits
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7
REVIEWER: sol-review-N-d
LEAN_STATUS: PROVED
LEAN_REF: resonant_prop2 (KAM/Nekhoroshev/Stability/ResonantStability.lean)
LEAN_NOTE: audit S7-8 PASS WITH NOTES, rows p2-concl Prop2Concl (R:89), Prop2Concl.wrap (R:161: max-norm consequence), prop2_core at S7-8-audit-1.md:97; resonant_prop2 exact signature S7-8-audit-1.md:103.
NOTE: -

NODE: bpN:p7:s-energy#rs
KIND: definition
TITLE: The resonant setting (RS)
STATEMENT_SOURCE: blueprint-N/parts/p7-stability.tex#bpN:p7:s-energy#rs@L178-L179
PROOF_SOURCE: -
CONTRACT_ID: bpN:p7:s-energy#rs
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n>=1; D subset R^n; r,s>0; Lambda subset Z^n; h holomorphic on V_rD and real on U_rD; 0<m<=M with ‖Q(I)‖_{2->2}<=M on U_rD; g,f_* in O(r,s)^R of finite norm with P_Lambda g=g; zeta>=|g|_{r,s}+|f_*|_{r,s}; eta=|f_*|_{r,s}; H=h+g+f_*; delta>0 with D delta-close to exact Lambda-resonances, delta<=mr/4, zeta<=mr^2/32; rho:=delta/(4M) (<=r/16)
SOURCE_QUANTIFIERS: n; D; r; s; Lambda; h; m; M; g; f_*; zeta; eta; delta
SOURCE_CONCLUSION: defines the resonant setting (RS) and rho=delta/(4M)<=r/16; an initial action I_0 is admissible if ‖I_0-J_0‖_2<rho for some J_0 in D
CONSTANT_SCOPE: m<=M, delta, zeta are data of (RS); rho is determined by (delta,M)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p7:setting, bpN:p7:resonance-data, bpN:p4:norm, bpN:p4:projections, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p7:setting | blueprint-N/parts/p7-stability.tex#bpN:p7:s-energy#rs@L178-L178 | U_rD, W_r, O(r,s)^R, h_R, omega, Q
EDGE: bpN:p7:resonance-data | blueprint-N/parts/p7-stability.tex#bpN:p7:s-energy#rs@L178-L178 | delta-closeness to exact Lambda-resonances, Hessian bound M
EDGE: bpN:p4:norm | blueprint-N/parts/p7-stability.tex#bpN:p7:s-energy#rs@L178-L178 | norms ¦g¦_{r,s}, ¦f_*¦_{r,s}
EDGE: bpN:p4:projections | blueprint-N/parts/p7-stability.tex#bpN:p7:s-energy#rs@L178-L178 | P_Lambda g=g
EDGE: bpN:p4:domains | blueprint-N/parts/p7-stability.tex#bpN:p7:s-energy#rs@L178-L178 | the consumer uses V_rD, D_{r,s} or a strip directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p7+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: ResSetting, resRho, IsAdmissible (KAM/Nekhoroshev/Stability/Resonant.lean)
LEAN_NOTE: audit S7-6 PASS WITH NOTES
NOTE: section-data node for coverage item p7:prose-L178-L179 (SPEC): a package for Lemmas admissible, no-exit and Lemma 2

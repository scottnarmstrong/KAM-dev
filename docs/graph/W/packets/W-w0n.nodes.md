NODE: bpW:w0n:recon-bounded
KIND: lemma
TITLE: Reconstruction is bounded into $C^k$
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:recon-bounded@L18-L27
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:recon-bounded@L29-L35
CONTRACT_ID: bpW:w0n:recon-bounded
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a > 0, p in R, k in N; c in l^{a,p}_C (also the standing m > 0 for the U_m, V_m clause)
SOURCE_QUANTIFIERS: for all a > 0, p, k; for all c
SOURCE_CONCLUSION: sum_j ¦c_j¦ j^k <= M_{a,p,k} ¦¦c¦¦_{a,p} with M_{a,p,k}^2 = sum_j j^{2k-2p} e^{-2aj} < infinity; the series sum c_j phi_j and its termwise x-derivatives of order <= k converge absolutely and uniformly on [0,pi]; c -> sum c_j phi_j is bounded linear l^{a,p} -> C^k([0,pi]) with norm <= sqrt(2/pi) M_{a,p,k}, vanishes at x = 0, pi, and int_0^pi (sum c_j phi_j) phi_l = c_l; U_m, V_m and q -> U_m(lambda q) are bounded linear l^{a,p} -> C^k([0,pi]) for every p, since lambda_j^{+-1/2} <= (1+m)^{1/4} j^{1/2} and multiplication by lambda^r maps l^{a,p} into l^{a,p-¦r¦} (0 <= r <= 2) with norm <= (1+m)^{r/2}
CONSTANT_SCOPE: M_{a,p,k} depends only on a, p, k; the multiplier norms on m
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:ellap#ellWeight, bpW:w0:basis#sineMode, bpW:w1:ext-unifderiv, bpW:w0:reconstruction#reconU, bpW:w0:reconstruction#reconV, bpW:w0:basis#lam, bpW:w0:mass
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:ellap#ellWeight | blueprint-W/parts/w0-normalization.tex#bpW:w0n:recon-bounded@L30-L30 | the norm ¦¦c¦¦_{a,p} with weight j^p e^{aj} in Cauchy-Schwarz
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w0-normalization.tex#bpW:w0n:recon-bounded@L31-L31 | ¦d_x^r phi_j¦ <= sqrt(2/pi) j^r; phi_j(0) = phi_j(pi) = 0; orthonormality
EDGE: bpW:w1:ext-unifderiv | blueprint-W/parts/w0-normalization.tex#bpW:w0n:recon-bounded@L32-L32 | Weierstrass M-test and termwise differentiation of uniformly convergent derivative series
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w0-normalization.tex#bpW:w0n:recon-bounded@L24-L24 | U_m is a series of this form with c_j = q_j/sqrt(lambda_j)
EDGE: bpW:w0:reconstruction#reconV | blueprint-W/parts/w0-normalization.tex#bpW:w0n:recon-bounded@L24-L24 | V_m is a series of this form with c_j = sqrt(lambda_j) p_j
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#bpW:w0n:recon-bounded@L25-L25 | the multiplier lambda^r and the bound lambda_j^{+-1/2} <= (1+m)^{1/4} j^{1/2}
EDGE: bpW:w0:mass | blueprint-W/parts/w0-normalization.tex#bpW:w0n:recon-bounded@L34-L34 | j^2 + m <= (1+m) j^2 uses m >= 0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w0n:quartic-coeff
KIND: lemma
TITLE: Closed form, (c)
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:quartic-coeff@L40-L51
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:quartic-coeff@L53-L69
CONTRACT_ID: bpW:w0n:quartic-coeff
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: i, j, k, l >= 1; g_ijkl = int_0^pi phi_i phi_j phi_k phi_l dx
SOURCE_QUANTIFIERS: for all i, j, k, l >= 1
SOURCE_CONCLUSION: g_ijkl = (1/(2pi)) ([i+l=j+k] + [i+k=j+l] + [i+j=k+l] - [i=j+k+l] - [j=i+k+l] - [k=i+j+l] - [l=i+j+k]); g is symmetric; g_ijkl = 0 unless +-i+-j+-k+-l = 0; g_iiii = 3/(2pi); g_iijj = 1/pi (i != j); equivalently (bpW:w0n:g-signed) g_ijkl = (1/(2pi)) sum_{eps in {+-1}^3} s(eps) [l = eps_1 i + eps_2 j + eps_3 k], s(eps) = (-1)^{1+#{t: eps_t = -1}}, so ¦g_ijkl¦ <= (1/(2pi)) sum_eps [l = eps_1 i + eps_2 j + eps_3 k]
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#sineMode, stepW:w0n:prod, stepW:w0n:cos, stepW:w0n:signed
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w0-normalization.tex#bpW:w0n:quartic-coeff@L41-L41 | g is the integral of a product of four modes phi
EDGE: stepW:w0n:prod | blueprint-W/parts/w0-normalization.tex#bpW:w0n:quartic-coeff@L54-L54 | proof step
EDGE: stepW:w0n:cos | blueprint-W/parts/w0-normalization.tex#bpW:w0n:quartic-coeff@L57-L57 | proof step
EDGE: stepW:w0n:signed | blueprint-W/parts/w0-normalization.tex#bpW:w0n:quartic-coeff@L65-L65 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:prod
KIND: step
TITLE: Product to sum
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:prod@L54-L56
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:prod@L54-L56
CONTRACT_ID: stepW:w0n:prod
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: i, j, k, l >= 1
SOURCE_QUANTIFIERS: for all x
SOURCE_CONCLUSION: phi_i phi_j phi_k phi_l = (1/pi^2)(cos(i-j)x - cos(i+j)x)(cos(k-l)x - cos(k+l)x)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#sineMode
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w0-normalization.tex#stepW:w0n:prod@L56-L56 | phi_j = sqrt(2/pi) sin(jx) and the product-to-sum formula
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:cos
KIND: step
TITLE: Cosine integrals
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:cos@L57-L64
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:cos@L57-L64
CONTRACT_ID: stepW:w0n:cos
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: i,j,k,l >= 1; A,B in Z (auxiliary integration variables)
SOURCE_QUANTIFIERS: for every choice of the source data stated in SOURCE_HYPOTHESES; m > 0 fixed under the standing assumption
SOURCE_CONCLUSION: int_0^pi cos Ax cos Bx dx = (pi/2)([A=B] + [A=-B]); hence the eight-bracket formula for g_ijkl, which reduces to the stated closed form, with g_iiii = 3/(2pi) and g_iijj = 1/pi (i != j)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w0n:prod
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w0n:prod | blueprint-W/parts/w0-normalization.tex#stepW:w0n:cos@L60-L60 | integrates the product-to-sum expansion termwise
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: sol-delta-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:signed
KIND: step
TITLE: Signed form
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:signed@L65-L68
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:signed@L65-L68
CONTRACT_ID: stepW:w0n:signed
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: i,j,k,l >= 1
SOURCE_QUANTIFIERS: for all i, j, k, l >= 1
SOURCE_CONCLUSION: the seven bracket relations solved for l give the signed form (bpW:w0n:g-signed) (the eighth pattern l = -i-j-k is impossible for l >= 1)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w0n:cos
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w0n:cos | blueprint-W/parts/w0-normalization.tex#stepW:w0n:signed@L66-L66 | rewrites the seven relations of the closed form
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: sol-delta-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w0n:gradient
KIND: lemma
TITLE: $G$ and its gradient as absolutely convergent sums
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:gradient@L76-L83
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:gradient@L85-L93
CONTRACT_ID: bpW:w0n:gradient
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a > 0, p >= 0, q in l^{a,p}; hat q_j = q_j/sqrt(lambda_j); G and G_q taken on l^{a,p} (Definitions bpW:w0:H and bpW:w0:Gq)
SOURCE_QUANTIFIERS: for all a > 0, p >= 0, q
SOURCE_CONCLUSION: G(q) = (1/4) sum_{i,j,k,l} g_ijkl hat q_i hat q_j hat q_k hat q_l and G_q(q)_l = (1/sqrt(lambda_l)) sum_{i,j,k} g_ijkl hat q_i hat q_j hat q_k, both absolutely convergent; G is Gateaux differentiable along every coordinate with dG/dq_l = G_q(q)_l; int_0^pi U_m(q)^3 phi_l dx = sqrt(lambda_l) G_q(q)_l
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:recon-bounded, bpW:w0:reconstruction#reconU, bpW:w0:H, bpW:w0n:quartic-coeff, bpW:w1:ext-integral, bpW:w0:Gq#cubicGrad, bpW:w0:basis#lam, bpW:w0:basis#sineMode
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:recon-bounded | blueprint-W/parts/w0-normalization.tex#bpW:w0n:gradient@L86-L86 | k = 0: sum ¦hat q_j¦ < infinity and U_m(q) = sum hat q_j phi_j uniformly
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w0-normalization.tex#bpW:w0n:gradient@L86-L86 | U_m(q) = sum hat q_j phi_j
EDGE: bpW:w0:H | blueprint-W/parts/w0-normalization.tex#bpW:w0n:gradient@L89-L89 | G(q) = (1/4) int U_m(q)^4
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w0-normalization.tex#bpW:w0n:gradient@L87-L87 | the coefficients g_ijkl of the termwise-integrated quadruple series
EDGE: bpW:w1:ext-integral | blueprint-W/parts/w0-normalization.tex#bpW:w0n:gradient@L88-L88 | termwise integration (dominated convergence for series) and differentiation under the integral
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w0-normalization.tex#bpW:w0n:gradient@L91-L91 | identifies int U_m(q)^3 phi_l / sqrt(lambda_l) with G_q(q)_l
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#bpW:w0n:gradient@L77-L78 | lambda occurs explicitly in the local source statement or calculation
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w0-normalization.tex#bpW:w0n:gradient@L87-L87 | frozen definition is used by its symbol; coefficients q,p are unweighted, as in the blueprint
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n+claude-suborch-W-r2
REVIEWER: sol-delta3-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Writer revision r2 (wave-1 corpus update, inp 99afc128 blueprint cleanup): the statement now names the domain l^{a,p} of G and G_q (L78-L79).

NODE: bpW:w0n:algebra
KIND: lemma
TITLE: Weighted convolution algebra
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:algebra@L95-L99
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:algebra@L101-L114
CONTRACT_ID: bpW:w0n:algebra
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a >= 0, s >= 1; c, d in l^{a,s}_b
SOURCE_QUANTIFIERS: for all a >= 0, s >= 1, c, d
SOURCE_CONCLUSION: ¦¦c*d¦¦_{a,s} <= K_s ¦¦c¦¦_{a,s} ¦¦d¦¦_{a,s} with K_s = 2^s (1+2 zeta(2s))^{1/2}; K_{3/2}^2 = 8(1+2 zeta(3)); each convolution sum converges absolutely
CONSTANT_SCOPE: K_s depends only on s
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:twosided, stepW:w0n:weight, stepW:w0n:young
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:twosided | blueprint-W/parts/w0-normalization.tex#bpW:w0n:algebra@L96-L96 | the two-sided spaces and the convolution
EDGE: stepW:w0n:weight | blueprint-W/parts/w0-normalization.tex#bpW:w0n:algebra@L103-L103 | proof step
EDGE: stepW:w0n:young | blueprint-W/parts/w0-normalization.tex#bpW:w0n:algebra@L108-L108 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:weight
KIND: step
TITLE: Weight inequality
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:weight@L103-L107
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:weight@L103-L107
CONTRACT_ID: stepW:w0n:weight
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a >= 0, s >= 1; w_l = <l>^s e^{a¦l¦}
SOURCE_QUANTIFIERS: for all i, l in Z
SOURCE_CONCLUSION: e^{a¦l¦} <= e^{a¦i¦} e^{a¦l-i¦}, <l> <= <i> + <l-i>, and w_l <= 2^{s-1}(w_i w_{l-i}/<l-i>^s + w_i w_{l-i}/<i>^s)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:twosided
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:twosided | blueprint-W/parts/w0-normalization.tex#stepW:w0n:weight@L104-L104 | the weight <l> = max(1,¦l¦) of l^{a,s}_b
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:young
KIND: step
TITLE: Young and Cauchy--Schwarz
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:young@L108-L113
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:young@L108-L113
CONTRACT_ID: stepW:w0n:young
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a >= 0, s >= 1; c,d in l_b^{a,s}; w_l = <l>^s exp(a abs(l)); C_l = w_l abs(c_l), D_l = w_l abs(d_l); C'_l=C_l/<l>^s, D'_l=D_l/<l>^s
SOURCE_QUANTIFIERS: for every choice of the source data stated in SOURCE_HYPOTHESES; m > 0 fixed under the standing assumption
SOURCE_CONCLUSION: w_l ¦(c*d)_l¦ <= 2^{s-1}((C*D')_l + (C'*D)_l); with Young ¦¦X*Y¦¦_2 <= ¦¦X¦¦_2 ¦¦Y¦¦_1 and ¦¦D'¦¦_1 <= ¦¦D¦¦_2 (1+2 zeta(2s))^{1/2} this gives the bound with K_s and the absolute convergence
CONSTANT_SCOPE: K_s depends only on s
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w0n:weight, bpW:w1:young
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w0n:weight | blueprint-W/parts/w0-normalization.tex#stepW:w0n:young@L109-L109 | inserts the weight inequality
EDGE: bpW:w1:young | blueprint-W/parts/w0-normalization.tex#stepW:w0n:young@L110-L110 | Young's inequality (i) and the l^1 control with 1+2 zeta(2s) (ii)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: sol-delta-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w0n:cubic-bound
KIND: theorem
TITLE: Cubic gradient, (b)
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L119-L131
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L133-L157
CONTRACT_ID: bpW:w0n:cubic-bound
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a >= 0, p >= 1/2; T(q,q',q'')_l = (1/sqrt(lambda_l)) sum_{i,j,k} g_ijkl hat q_i hat q'_j hat q''_k on (l^{a,p}_C)^3, hat q_j = q_j/sqrt(lambda_j)
SOURCE_QUANTIFIERS: for all a >= 0, p >= 1/2; for all q, q', q''
SOURCE_CONCLUSION: the sums converge absolutely; T is a bounded symmetric trilinear map into l^{a,p+1}_C, real on real arguments, with ¦¦T(q,q',q'')¦¦_{a,p+1} <= C_* ¦¦q¦¦ ¦¦q'¦¦ ¦¦q''¦¦, C_* = K_{p+1/2}^2/pi; for a > 0 and real q in l^{a,p}, G_q(q) = T(q,q,q) (Definition bpW:w0:Gq on l^{a,p}); for a = p = 1, G_q : l^{1,1} -> l^{1,2} is real analytic (a continuous cubic polynomial) with ¦¦G_q(q)¦¦_{1,2} <= C_m ¦¦q¦¦_{1,1}^3, C_m = 8(1+2 zeta(3))/pi (about 8.67)
CONSTANT_SCOPE: C_* depends only on p; C_m is independent of m > 0 (only lambda_j >= j is used)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:quartic-coeff, bpW:w0:basis#lam, bpW:w0:Gq#cubicGrad, stepW:w0n:majorant, stepW:w0n:selection, stepW:w0n:smoothing, stepW:w0n:analytic, bpW:w0n:gradient, bpW:w0n:algebra
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L121-L121 | the coefficients g_ijkl of T
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L121-L121 | the weights 1/sqrt(lambda)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L126-L127 | the identification G_q(q) = T(q,q,q)
EDGE: stepW:w0n:majorant | blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L134-L134 | proof step
EDGE: stepW:w0n:selection | blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L138-L138 | proof step
EDGE: stepW:w0n:smoothing | blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L144-L144 | proof step
EDGE: stepW:w0n:analytic | blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L151-L151 | proof step
EDGE: bpW:w0n:gradient | blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L126-L127 | explicit citation identifying G_q with the diagonal T
EDGE: bpW:w0n:algebra | blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L125-L125 | K_{p+1/2} is the algebra constant, with p >= 1/2 ensuring s >= 1
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n+claude-suborch-W-r2
REVIEWER: sol-delta3-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Writer revision r2 (wave-1 corpus update, inp 99afc128 blueprint cleanup): the identification G_q = T(q,q,q) is stated for real q in l^{a,p} with Definition bpW:w0:Gq on l^{a,p} (L126-L127).

NODE: stepW:w0n:majorant
KIND: step
TITLE: Even majorants
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:majorant@L134-L137
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:majorant@L134-L137
CONTRACT_ID: stepW:w0n:majorant
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a >= 0, p >= 1/2; q,q',q'' in l_C^{a,p}; define x_i=abs(q_abs(i))/sqrt(lambda_abs(i)) for i != 0 and x_0=0, and similarly x',x''
SOURCE_QUANTIFIERS: for every choice of the source data stated in SOURCE_HYPOTHESES; m > 0 fixed under the standing assumption
SOURCE_CONCLUSION: x is even and ¦¦x¦¦_{a,p+1/2}^2 = 2 sum_i (i/lambda_i) i^{2p} e^{2ai} ¦q_i¦^2 <= 2 ¦¦q¦¦_{a,p}^2 (the corrected constant sqrt 2, errata N-1)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:twosided, bpW:w0:basis#lambda-facts, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:twosided | blueprint-W/parts/w0-normalization.tex#stepW:w0n:majorant@L137-L137 | the two-sided norm of the majorant
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w0-normalization.tex#stepW:w0n:majorant@L136-L136 | lambda_i >= i (i/lambda_i < 1)
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#stepW:w0n:majorant@L135-L135 | lambda occurs explicitly in the local source statement or calculation
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: sol-delta-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:selection
KIND: step
TITLE: Selection rule bound
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:selection@L138-L143
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:selection@L138-L143
CONTRACT_ID: stepW:w0n:selection
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a >= 0, p >= 1/2; q,q',q'' in l_C^{a,p}; l >= 1; hat q and even majorants are the explicit sequences defined at L121-L122 and L135-L136
SOURCE_QUANTIFIERS: for every choice of the source data stated in SOURCE_HYPOTHESES; m > 0 fixed under the standing assumption
SOURCE_CONCLUSION: sum_{i,j,k} ¦g_ijkl¦ ¦hat q_i hat q'_j hat q''_k¦ <= (1/(2pi)) (x*x'*x'')_l, so the sum defining T converges absolutely
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:quartic-coeff, stepW:w0n:majorant, bpW:w0n:algebra
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w0-normalization.tex#stepW:w0n:selection@L139-L139 | the signed form (bpW:w0n:g-signed) and its bound
EDGE: stepW:w0n:majorant | blueprint-W/parts/w0-normalization.tex#stepW:w0n:selection@L141-L141 | the even majorants x, x', x''
EDGE: bpW:w0n:algebra | blueprint-W/parts/w0-normalization.tex#stepW:w0n:selection@L143-L143 | finiteness of the triple convolution: apply the algebra estimate twice, s=p+1/2 >= 1
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: sol-delta-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:smoothing
KIND: step
TITLE: Smoothing
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:smoothing@L144-L150
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:smoothing@L144-L150
CONTRACT_ID: stepW:w0n:smoothing
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a >= 0, p >= 1/2; q,q',q'' in l_C^{a,p}; s=p+1/2; X=x*x'*x'' with the explicit majorants of L135-L136
SOURCE_QUANTIFIERS: for every choice of the source data stated in SOURCE_HYPOTHESES; m > 0 fixed under the standing assumption
SOURCE_CONCLUSION: ¦¦T¦¦_{a,p+1}^2 <= (1/(8 pi^2)) ¦¦X¦¦_{a,p+1/2}^2 and ¦¦X¦¦ <= K_s^2 2^{3/2} prod ¦¦q¦¦, hence ¦¦T¦¦_{a,p+1} <= (K_s^2/pi) prod ¦¦q¦¦
CONSTANT_SCOPE: K_s depends only on s = p + 1/2
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w0n:selection, bpW:w0:basis#lambda-facts, bpW:w0n:algebra, stepW:w0n:majorant, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w0n:selection | blueprint-W/parts/w0-normalization.tex#stepW:w0n:smoothing@L145-L145 | the pointwise bound by X_l/(2pi)
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w0-normalization.tex#stepW:w0n:smoothing@L145-L145 | l/lambda_l <= 1
EDGE: bpW:w0n:algebra | blueprint-W/parts/w0-normalization.tex#stepW:w0n:smoothing@L148-L148 | the algebra bound with s = p + 1/2 >= 1, applied twice
EDGE: stepW:w0n:majorant | blueprint-W/parts/w0-normalization.tex#stepW:w0n:smoothing@L149-L149 | ¦¦x¦¦ <= sqrt 2 ¦¦q¦¦
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#stepW:w0n:smoothing@L145-L145 | lambda occurs explicitly in the local source statement or calculation
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: sol-delta-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:analytic
KIND: step
TITLE: Analyticity
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:analytic@L151-L156
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:analytic@L151-L156
CONTRACT_ID: stepW:w0n:analytic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a >= 0, p >= 1/2; q in l_C^{a,p}; T is the series formula of L121-L122 (boundedness and symmetry are proved, not assumed)
SOURCE_QUANTIFIERS: for every choice of the source data stated in SOURCE_HYPOTHESES; m > 0 fixed under the standing assumption
SOURCE_CONCLUSION: T is trilinear and symmetric; q -> T(q,q,q) is a continuous homogeneous cubic polynomial, analytic on the whole space, real on real sequences; for a > 0 it is G_q (Lemma bpW:w0n:gradient)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:quartic-coeff, bpW:w1:ext-analytic, bpW:w0n:gradient, bpW:w0:Gq#cubicGrad, stepW:w0n:smoothing
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w0-normalization.tex#stepW:w0n:analytic@L152-L152 | symmetry of g
EDGE: bpW:w1:ext-analytic | blueprint-W/parts/w0-normalization.tex#stepW:w0n:analytic@L154-L154 | a continuous multilinear map (its diagonal) is analytic
EDGE: bpW:w0n:gradient | blueprint-W/parts/w0-normalization.tex#stepW:w0n:analytic@L156-L156 | identification with G_q for a > 0
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w0-normalization.tex#stepW:w0n:analytic@L156-L156 | frozen definition is used by its symbol; coefficients q,p are unweighted, as in the blueprint
EDGE: stepW:w0n:smoothing | blueprint-W/parts/w0-normalization.tex#stepW:w0n:analytic@L153-L153 | boundedness of the trilinear formula is supplied by the preceding smoothing estimate
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: sol-delta-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:force
KIND: step
TITLE: Force identity
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:force@L188-L194
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:force@L188-L194
CONTRACT_ID: stepW:w0n:force
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: q in l^{1,1}; f = U_m(q)^3 in C([0,pi])
SOURCE_QUANTIFIERS: for q
SOURCE_CONCLUSION: (bpW:w0n:force): U_m(q)^3 = sum_l sqrt(lambda_l) G_q(q)_l phi_l uniformly on [0,pi], and -d_x^2 U_m(q) + m U_m(q) = U_m(lambda^2 q)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:gradient, bpW:w0n:cubic-bound, bpW:w0n:recon-bounded, bpW:w1:sine-completeness, bpW:w0:basis#sineMode, bpW:w0:basis#lam, bpW:w0:reconstruction#reconU, bpW:w0:Gq#cubicGrad
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:gradient | blueprint-W/parts/w0-normalization.tex#stepW:w0n:force@L189-L189 | int f phi_l = sqrt(lambda_l) G_q(q)_l
EDGE: bpW:w0n:cubic-bound | blueprint-W/parts/w0-normalization.tex#stepW:w0n:force@L190-L190 | (sqrt(lambda_l) G_q(q)_l) lies in l^{1,1}
EDGE: bpW:w0n:recon-bounded | blueprint-W/parts/w0-normalization.tex#stepW:w0n:force@L190-L190 | uniform convergence of S (k = 0) and termwise differentiation (k = 2)
EDGE: bpW:w1:sine-completeness | blueprint-W/parts/w0-normalization.tex#stepW:w0n:force@L192-L192 | (phi_l) is a complete orthonormal system of L^2(0,pi)
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w0-normalization.tex#stepW:w0n:force@L194-L194 | -phi_j'' + m phi_j = lambda_j^2 phi_j
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#stepW:w0n:force@L194-L194 | the eigenvalue lambda_j^2 = j^2 + m
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w0-normalization.tex#stepW:w0n:force@L189-L189 | frozen definition is used by its symbol; coefficients q,p are unweighted, as in the blueprint
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w0-normalization.tex#stepW:w0n:force@L189-L189 | frozen definition is used by its symbol; coefficients q,p are unweighted, as in the blueprint
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: sol-delta-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w0n:nonres
KIND: lemma
TITLE: Qualitative nonresonance of all quartic terms
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:nonres@L222-L226
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:nonres@L228-L249
CONTRACT_ID: bpW:w0n:nonres
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0; a, b, c, d >= 1 with g_abcd != 0; sigma in {+-1}^4 with sigma_1 lambda_a + sigma_2 lambda_b + sigma_3 lambda_c + sigma_4 lambda_d = 0
SOURCE_QUANTIFIERS: for all m > 0, a, b, c, d, sigma
SOURCE_CONCLUSION: the indices with sigma = +1 and those with sigma = -1 form equal multisets (two of each)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#lam, bpW:w0n:quartic-coeff, stepW:w0n:31, stepW:w0n:22
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nonres@L224-L224 | the frequencies lambda
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nonres@L229-L229 | g_abcd != 0 implies a signed relation +-a+-b+-c+-d = 0
EDGE: stepW:w0n:31 | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nonres@L231-L231 | proof step
EDGE: stepW:w0n:22 | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nonres@L235-L235 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:31
KIND: step
TITLE: Four or three equal signs
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:31@L231-L234
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:31@L231-L234
CONTRACT_ID: stepW:w0n:31
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0; a,b,c,d >= 1 with g_abcd != 0; sigma in {+1,-1}^4; sum sigma_r lambda_index(r)=0; consider the cases of four or three equal signs
SOURCE_QUANTIFIERS: for every choice of the source data stated in SOURCE_HYPOTHESES; m > 0 fixed under the standing assumption
SOURCE_CONCLUSION: all four signs equal is impossible; three equal signs are impossible since lambda_x + lambda_y > lambda_{x+y} and lambda_d <= lambda_{a+b+c} < lambda_a + lambda_b + lambda_c
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#lambda-facts, bpW:w0:mass, bpW:w0:basis#lam, bpW:w0n:quartic-coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w0-normalization.tex#stepW:w0n:31@L233-L233 | lambda > 0 and j -> lambda_j increasing
EDGE: bpW:w0:mass | blueprint-W/parts/w0-normalization.tex#stepW:w0n:31@L234-L234 | squaring: 2 sqrt((x^2+m)(y^2+m)) > 2xy - m uses m > 0
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#stepW:w0n:31@L233-L233 | lambda occurs explicitly in the local source statement or calculation
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w0-normalization.tex#stepW:w0n:31@L233-L233 | g_abcd != 0 supplies d <= a+b+c via the selection rule at L229-L230
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: sol-delta-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:22
KIND: step
TITLE: Two against two
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:22@L235-L248
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:22@L235-L248
CONTRACT_ID: stepW:w0n:22
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0; a,b,c,d >= 1 with g_abcd != 0; lambda_a+lambda_b=lambda_c+lambda_d; {a,b} != {c,d} as multisets (contradiction case); f(s)=sqrt(s^2+m)
SOURCE_QUANTIFIERS: for every choice of the source data stated in SOURCE_HYPOTHESES; m > 0 fixed under the standing assumption
SOURCE_CONCLUSION: case (1) a+b = c+d, case (2) a+c = b+d, case (3) a = b+c+d each lead to a contradiction; the cases are exhaustive
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#lambda-facts, bpW:w0:basis#lam, bpW:w0n:quartic-coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w0-normalization.tex#stepW:w0n:22@L238-L238 | strict convexity of f, f' > 0 increasing
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#stepW:w0n:22@L236-L236 | lambda occurs explicitly in the local source statement or calculation
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w0-normalization.tex#stepW:w0n:22@L237-L237 | the signed index relation used in the exhaustive cases comes from L229-L230
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: sol-delta-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w0n:Qdef
KIND: definition
TITLE: Partial quartic normal form
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:Qdef@L272-L275
PROOF_SOURCE: -
CONTRACT_ID: bpW:w0n:Qdef
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: G^tan, G^nor and resonance as in bpW:w0n:birkhoff#data
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: defines bar G = the sum of the resonant monomials of G^tan (with coefficients) and the partial quartic normal form Lambda + bar G + G^nor
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:birkhoff#data, bpW:w0:H
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:birkhoff#data | blueprint-W/parts/w0-normalization.tex#bpW:w0n:Qdef@L273-L273 | resonant monomials of G^tan; G^nor
EDGE: bpW:w0:H | blueprint-W/parts/w0-normalization.tex#bpW:w0n:Qdef@L274-L274 | Lambda, the quadratic part of H
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w0n:AB
KIND: theorem
TITLE: Action coefficients, (d)
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:AB@L277-L288
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:AB@L290-L307
CONTRACT_ID: bpW:w0n:AB
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: J = {1,2}; m > 0; I = (I_1,I_2), Z = (I_j)_{j>=3}, I_j = ¦z_j¦^2
SOURCE_QUANTIFIERS: for every m > 0
SOURCE_CONCLUSION: bar G = (1/2)<AI,I> + <BI,Z> with A_ii = 9/(8 pi lambda_i^2), A_12 = A_21 = 3/(2 pi lambda_1 lambda_2), B_ji = 3/(2 pi lambda_j lambda_i) (j >= 3, i in J); equivalently A = (3/(8pi)) D(4 11^T - Id)D, D = diag(1/lambda_1, 1/lambda_2), (BI)_j = (3/(2 pi lambda_j))(I_1/lambda_1 + I_2/lambda_2); and (bpW:w0n:avgG) <G> = (3/(16 pi))(4 (sum_j I_j/lambda_j)^2 - sum_j I_j^2/lambda_j^2)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:Qdef, bpW:w0:actions, bpW:w0:basis#lam, stepW:w0n:resavg, stepW:w0n:moments, stepW:w0n:sum
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:Qdef | blueprint-W/parts/w0-normalization.tex#bpW:w0n:AB@L279-L279 | bar G is the resonant tangential part
EDGE: bpW:w0:actions | blueprint-W/parts/w0-normalization.tex#bpW:w0n:AB@L278-L278 | I_j = ¦z_j¦^2, tangential I, normal Z
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#bpW:w0n:AB@L280-L280 | lambda in A and B
EDGE: stepW:w0n:resavg | blueprint-W/parts/w0-normalization.tex#bpW:w0n:AB@L291-L291 | proof step
EDGE: stepW:w0n:moments | blueprint-W/parts/w0-normalization.tex#bpW:w0n:AB@L297-L297 | proof step
EDGE: stepW:w0n:sum | blueprint-W/parts/w0-normalization.tex#bpW:w0n:AB@L301-L301 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:resavg
KIND: step
TITLE: Resonant equals averaged
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:resavg@L291-L296
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:resavg@L291-L296
CONTRACT_ID: stepW:w0n:resavg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the monomials of (bpW:w0n:Gz) with nonzero coefficient
SOURCE_QUANTIFIERS: monomials z^alpha zbar^beta
SOURCE_CONCLUSION: a monomial is resonant iff alpha = beta (it is I_a I_b); the angle average of z^alpha zbar^beta is delta_{alpha beta} I^alpha; hence bar G is the part of <G> (extended from finitely supported q by the absolutely convergent formula) with at least one tangential action
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:nonres, bpW:w0n:birkhoff#data, bpW:w0:actions, bpW:w0n:Qdef, bpW:w0n:gradient
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:nonres | blueprint-W/parts/w0-normalization.tex#stepW:w0n:resavg@L292-L292 | resonance with nonzero coefficient forces alpha = beta
EDGE: bpW:w0n:birkhoff#data | blueprint-W/parts/w0-normalization.tex#stepW:w0n:resavg@L292-L292 | the monomials of (bpW:w0n:Gz)
EDGE: bpW:w0:actions | blueprint-W/parts/w0-normalization.tex#stepW:w0n:resavg@L293-L293 | z_j = sqrt(I_j) e^{-i phi_j}
EDGE: bpW:w0n:Qdef | blueprint-W/parts/w0-normalization.tex#stepW:w0n:resavg@L294-L294 | bar G as the resonant tangential monomials
EDGE: bpW:w0n:gradient | blueprint-W/parts/w0-normalization.tex#stepW:w0n:resavg@L296-L296 | absolute convergence justifies extension of the finite-support average
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: sol-delta-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:moments
KIND: step
TITLE: Averages of monomials
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:moments@L297-L300
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:moments@L297-L300
CONTRACT_ID: stepW:w0n:moments
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: q_j = sqrt(2 I_j) cos phi_j, independent angles
SOURCE_QUANTIFIERS: indices i, j, k, l
SOURCE_CONCLUSION: <q_i q_j q_k q_l> = 0 unless the indices pair up; <q_i^4> = (3/2) I_i^2; <q_i^2 q_j^2> = I_i I_j (i != j); (i,i,i,i) occurs once and {i,i,j,j} six times among ordered quadruples
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:actions
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:actions | blueprint-W/parts/w0-normalization.tex#stepW:w0n:moments@L298-L298 | q_j = sqrt(2 I_j) cos phi_j
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:sum
KIND: step
TITLE: Summation
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:sum@L301-L306
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:sum@L301-L306
CONTRACT_ID: stepW:w0n:sum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0; oscillator actions I_j=abs(z_j)^2; y_j=I_j/lambda_j; first compute on finite support and extend as at L295-L296
SOURCE_QUANTIFIERS: for every choice of the source data stated in SOURCE_HYPOTHESES; m > 0 fixed under the standing assumption
SOURCE_CONCLUSION: <G> = (9/(16pi)) sum y_i^2 + (3/(2pi)) sum_{i<j} y_i y_j, which is (bpW:w0n:avgG); matching gives A and B
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:gradient, bpW:w0n:quartic-coeff, stepW:w0n:moments, stepW:w0n:resavg, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:gradient | blueprint-W/parts/w0-normalization.tex#stepW:w0n:sum@L302-L302 | G = (1/4) sum g_ijkl hat q^4 with hat q = q/sqrt(lambda)
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w0-normalization.tex#stepW:w0n:sum@L302-L302 | g_iiii = 3/(2pi), g_iijj = 1/pi
EDGE: stepW:w0n:moments | blueprint-W/parts/w0-normalization.tex#stepW:w0n:sum@L303-L303 | the moments 3/2 I^2, I_i I_j and the multiplicities
EDGE: stepW:w0n:resavg | blueprint-W/parts/w0-normalization.tex#stepW:w0n:sum@L305-L305 | bar G = the part of <G> with a tangential action
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#stepW:w0n:sum@L302-L302 | lambda occurs explicitly in the local source statement or calculation
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: sol-delta-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w0n:nondeg
KIND: theorem
TITLE: Nondegeneracy, (e)
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg@L348-L355
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg@L357-L379
CONTRACT_ID: bpW:w0n:nondeg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: J = {1,2}; m > 0; A, B of Theorem bpW:w0n:AB; (A1)-(A3) as in bpW:w0n:nondeg-sec#data
SOURCE_QUANTIFIERS: for every m > 0
SOURCE_CONCLUSION: (i) det A = -63/(64 pi^2 lambda_1^2 lambda_2^2) = -63/(64 pi^2 (1+m)(4+m)) != 0; (ii) <l,lambda_N> != 0 for 1 <= ¦l¦ <= 2; (iii) (A3) holds
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:nondeg-sec#data, bpW:w0n:AB, stepW:w0n:det, stepW:w0n:A2, stepW:w0n:A3red, stepW:w0n:l1, stepW:w0n:l2, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:nondeg-sec#data | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg@L353-L353 | the conditions (A2), (A3)
EDGE: bpW:w0n:AB | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg@L351-L351 | the matrix A
EDGE: stepW:w0n:det | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg@L358-L358 | proof step
EDGE: stepW:w0n:A2 | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg@L362-L362 | proof step
EDGE: stepW:w0n:A3red | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg@L365-L365 | proof step
EDGE: stepW:w0n:l1 | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg@L371-L371 | proof step
EDGE: stepW:w0n:l2 | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg@L375-L375 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg@L351-L351 | lambda occurs explicitly in the local source statement or calculation
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: sol-delta-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:det
KIND: step
TITLE: Determinant
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:det@L358-L361
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:det@L358-L361
CONTRACT_ID: stepW:w0n:det
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0 fixed; J={1,2}; A defined by Theorem bpW:w0n:AB (not an additional assumed estimate)
SOURCE_QUANTIFIERS: for every m > 0; additionally for every integer n >= 1 in the parenthetical determinant identity
SOURCE_CONCLUSION: det A = (3/(8pi))^2 lambda_1^{-2} lambda_2^{-2} det((3,4),(4,3)) = -63/(64 pi^2) lambda_1^{-2} lambda_2^{-2}; also for general n >= 1, det(4 11^T - Id_n)=(-1)^{n-1}(4n-1)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:AB, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:AB | blueprint-W/parts/w0-normalization.tex#stepW:w0n:det@L359-L359 | A = (3/(8pi)) D(4 11^T - Id) D
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#stepW:w0n:det@L359-L359 | lambda occurs explicitly in the local source statement or calculation
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-delta-W-w0n
REVIEWER: sol-delta2-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:A2
KIND: step
TITLE: Pure normal
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:A2@L362-L364
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:A2@L362-L364
CONTRACT_ID: stepW:w0n:A2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0 fixed; l an integer sequence supported on N={j>=3}, with 1 <= sum_j abs(l_j) <= 2
SOURCE_QUANTIFIERS: for every m > 0 and every such l
SOURCE_CONCLUSION: <l,lambda_N> is +-lambda_a, +-2 lambda_a, +-(lambda_a+lambda_b) or +-(lambda_a-lambda_b), a != b in N, all nonzero
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#lambda-facts, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w0-normalization.tex#stepW:w0n:A2@L364-L364 | lambda > 0 strictly increasing
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#stepW:w0n:A2@L363-L363 | lambda occurs explicitly in the local source statement or calculation
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-delta-W-w0n
REVIEWER: sol-delta2-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:A3red
KIND: step
TITLE: Reduction of (A$_3$)
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:A3red@L365-L370
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:A3red@L365-L370
CONTRACT_ID: stepW:w0n:A3red
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0 fixed; k in Z^2, l an integer sequence on N={j>=3}, 1 <= sum_j abs(l_j) <= 2; b=(1/lambda_1,1/lambda_2), s=sum_{j>=3} l_j/lambda_j; A,B and the affine map are defined in the enclosing statement
SOURCE_QUANTIFIERS: for every m > 0 and every such (k,l); c is introduced only under vanishing of the linear part
SOURCE_CONCLUSION: A = (3/(8pi))(4bb^T - D^2), B^T l = (3/(2pi)) s b; the linear part (3/(8pi))(4(<b,k>+s)b - D^2 k) vanishes iff k_i/lambda_i = c (i = 1,2) with c = 4(<b,k>+s), then <b,k> = 2c, s = -(7/4)c; the constant part is c(lambda_1^2+lambda_2^2) + <l,lambda_N>
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:AB, bpW:w0n:nondeg-sec#data, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:AB | blueprint-W/parts/w0-normalization.tex#stepW:w0n:A3red@L367-L367 | A and B
EDGE: bpW:w0n:nondeg-sec#data | blueprint-W/parts/w0-normalization.tex#stepW:w0n:A3red@L368-L368 | the affine map of (A3)
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#stepW:w0n:A3red@L366-L366 | lambda occurs explicitly in the local source statement or calculation
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-delta-W-w0n
REVIEWER: sol-delta2-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:l1
KIND: step
TITLE: The case $\abs l=1$
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:l1@L371-L374
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:l1@L371-L374
CONTRACT_ID: stepW:w0n:l1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0; k in Z^2, l in Z^N finitely supported with abs(l)=1; l=sigma e_nu, sigma in {+1,-1}, nu >= 3; consider vanishing of the affine map in (A3)
SOURCE_QUANTIFIERS: for every choice of the source data stated in SOURCE_HYPOTHESES; m > 0 fixed under the standing assumption
SOURCE_CONCLUSION: the constant part vanishes iff 7 lambda_nu^2 = 4(lambda_1^2+lambda_2^2), and then k_i^2 in (0,4/7) is not the square of an integer; so (A3) holds
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w0n:A3red, bpW:w0:basis#lam, bpW:w0:basis#lambda-facts
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w0n:A3red | blueprint-W/parts/w0-normalization.tex#stepW:w0n:l1@L372-L372 | the vanishing conditions of the reduction
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#stepW:w0n:l1@L372-L372 | lambda occurs explicitly in the local source statement or calculation
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w0-normalization.tex#stepW:w0n:l1@L374-L374 | strict positivity of lambda makes k_i^2 strictly between zero and 4/7
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: sol-delta-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:l2
KIND: step
TITLE: The case $\abs l=2$
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:l2@L375-L378
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:l2@L375-L378
CONTRACT_ID: stepW:w0n:l2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0; k in Z^2, l in Z^N finitely supported with abs(l)=2; consider vanishing of the linear part of the affine map in (A3)
SOURCE_QUANTIFIERS: for every choice of the source data stated in SOURCE_HYPOTHESES; m > 0 fixed under the standing assumption
SOURCE_CONCLUSION: ¦s¦ <= 2/lambda_3 < 2/3, ¦c¦ < 8/21, k_2 - k_1 = c(lambda_2 - lambda_1) with 0 < lambda_2 - lambda_1 < 1 forces k_1 = k_2, c = 0, s = 0, impossible for ¦l¦ = 2; so the linear part does not vanish
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w0n:A3red, bpW:w0:basis#lambda-facts, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w0n:A3red | blueprint-W/parts/w0-normalization.tex#stepW:w0n:l2@L376-L376 | the vanishing conditions of the reduction
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w0-normalization.tex#stepW:w0n:l2@L377-L377 | lambda_3 > 3, 0 < lambda_2 - lambda_1 < 1, lambda injective
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#stepW:w0n:l2@L376-L376 | lambda occurs explicitly in the local source statement or calculation
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: sol-delta-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w0n:birkhoff#data
KIND: definition
TITLE: Quartic part in complex coordinates; resonance; tangential/normal split
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:birkhoff@L260-L270
PROOF_SOURCE: -
CONTRACT_ID: bpW:w0n:birkhoff#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: J = {1,2}, N = {j >= 3}; complex coordinates z of Definition bpW:w0:z
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: defines (with the identity (bpW:w0n:Gz)) G = (1/16) sum g_ijkl (lambda_i lambda_j lambda_k lambda_l)^{-1/2} prod (z + zbar) as a sum of monomials z^alpha zbar^beta, ¦alpha¦+¦beta¦ = 4, evolving by e^{-i<alpha-beta,hat lambda>t} along the linear flow; resonant iff <alpha-beta,hat lambda> = 0; the split G = G^tan + G^nor, G^nor the monomials with all indices in N
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:z, bpW:w0n:gradient, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:z | blueprint-W/parts/w0-normalization.tex#bpW:w0n:birkhoff@L261-L261 | q_j = (z_j + zbar_j)/sqrt 2 and the linear flow dz_j = -i lambda_j z_j
EDGE: bpW:w0n:gradient | blueprint-W/parts/w0-normalization.tex#bpW:w0n:birkhoff@L263-L263 | G = (1/4) sum g_ijkl q-hat^4 (quartic series)
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#bpW:w0n:birkhoff@L263-L263 | the weights (lambda_i lambda_j lambda_k lambda_l)^{-1/2}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Unlabelled prose L260-L270 (with the display bpW:w0n:Gz) that fixes data consumed by Qdef, AB and formal-birkhoff (SPEC section-data rule).

NODE: bpW:w0n:nondeg-sec#data
KIND: definition
TITLE: Nondegeneracy conditions (A1)-(A3) of the Cantor Manifold Theorem
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg-sec@L343-L346
PROOF_SOURCE: -
CONTRACT_ID: bpW:w0n:nondeg-sec#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: A, B of Theorem bpW:w0n:AB
SOURCE_QUANTIFIERS: (k,l) in Z^2 x Z^N with 1 <= ¦l¦ <= 2
SOURCE_CONCLUSION: defines omega(I) = lambda_J + A I, Omega(I) = lambda_N + B I and the conditions (A1) det A != 0, (A2) <l,lambda_N> != 0, (A3) <k,omega(I)> + <l,Omega(I)> not identically 0 as an affine function of I, for all (k,l) with 1 <= ¦l¦ <= 2 (¦l¦ = sum ¦l_j¦)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:AB, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:AB | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg-sec@L343-L343 | omega(I) = lambda_J + A I and Omega(I) = lambda_N + B I
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg-sec@L343-L343 | lambda occurs explicitly in the local source statement or calculation
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: sol-delta-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Unlabelled prose L343-L346 defining the conditions stated in Theorem bpW:w0n:nondeg (SPEC section-data rule).

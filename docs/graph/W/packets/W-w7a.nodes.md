NODE: bpW:w7:ext-tonelli
KIND: external
TITLE: Slicing (Tonelli)
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:ext-tonelli@L47-L51
PROOF_SOURCE: -
CONTRACT_ID: bpW:w7:ext-tonelli
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: for Borel S subset R^2, Leb(S) = int Leb_1{t : (t,y) in S} dy = int Leb_1{t : (y,t) in S} dy
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w7:ext-diam
KIND: external
TITLE: Sets of small diameter on the line
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:ext-diam@L52-L54
PROOF_SOURCE: -
CONTRACT_ID: bpW:w7:ext-diam
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: a set S subset R with ¦t - t'¦ <= d for all t, t' in S has Leb_1(S) <= d
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w7:ext-linear
KIND: external
TITLE: Lebesgue measure under affine maps
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:ext-linear@L55-L57
PROOF_SOURCE: -
CONTRACT_ID: bpW:w7:ext-linear
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: Leb(T(S) + c) = ¦det T¦ Leb(S) for invertible linear T of R^2 and c in R^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w7:ext-borel
KIND: external
TITLE: Borel sets
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:ext-borel@L58-L65
PROOF_SOURCE: -
CONTRACT_ID: bpW:w7:ext-borel
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: if D subset R^2 is Borel and f : D -> R continuous on D then {xi in D : ¦f(xi)¦ < eta} is Borel; countable unions, intersections, differences of Borel sets are Borel; Z^2 and the finitely supported l with ¦l¦ <= 2 are countable; measure is countably subadditive and monotone
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w7:ext-zeta
KIND: external
TITLE: Lattice sums
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:ext-zeta@L66-L68
PROOF_SOURCE: -
CONTRACT_ID: bpW:w7:ext-zeta
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: #{k in Z^2 : ¦k¦ = N} = 4N for N >= 1; sum N^{-2} = pi^2/6; hence Z_3 = sum_{k != 0} ¦k¦^{-3} = 4 zeta(2) = 2 pi^2/3 < 7
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w7:ext-ball
KIND: external
TITLE: Max-norm balls
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:ext-ball@L69-L71
PROOF_SOURCE: -
CONTRACT_ID: bpW:w7:ext-ball
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: Metric.ball 0 h in Fin 2 -> R is (-h,h)^2; Leb of a product of intervals is the product of lengths
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w7:ext-ennreal
KIND: external
TITLE: Extended reals
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:ext-ennreal@L72-L76
PROOF_SOURCE: -
CONTRACT_ID: bpW:w7:ext-ennreal
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: extended-real arithmetic: x/y <= 1, (y - s)/y = 1 - s/y for 0 < x <= y < infinity, s <= x; squeeze to 1; real powers monotone, x^a x^b = x^{a+b}; ceil(x) <= 2x for x >= 1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w7:indexdef
KIND: definition
TITLE: Integer data
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:indexdef@L82-L98
PROOF_SOURCE: -
CONTRACT_ID: bpW:w7:indexdef
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W7 standing data (L33-L41): m > 0, lambda_j = sqrt(j^2+m), corrected A, B, max norms on R^2, Leb, ¦k¦ = ¦k_1¦ + ¦k_2¦
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: defines N_3, finitely supported l on N_3 with ¦l¦, <l,x>, e_j, Lambda = {1 <= ¦l¦ <= 2}, Lambda^-, Lambda^+, the Dirichlet weight <l> = max(1,¦sum j l_j¦) (<l> >= 3 on Lambda^+, <l> = i - j on Lambda^-), ¦l¦_delta, Z, the fixed exponents tau = 24, varpi = 1/2, beta = 1/4, A_k = 1 + ¦k¦^tau, and the modified weight hat w(l) = (i-j) j^{-1/4} on Lambda^-, <l> otherwise
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7#data | blueprint-W/parts/w7-measure.tex#bpW:w7:indexdef@L83-L83 | ¦k¦ and indices
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w7:omega0
KIND: definition
TITLE: Unperturbed frequencies
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:omega0@L127-L131
PROOF_SOURCE: -
CONTRACT_ID: bpW:w7:omega0
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W7 standing data (L33-L41): m > 0, lambda_j = sqrt(j^2+m), corrected A, B, max norms on R^2, Leb, ¦k¦ = ¦k_1¦ + ¦k_2¦; lambda_J = (lambda_1,lambda_2), b = (1/lambda_1, 1/lambda_2), A of Theorem bpW:w0n:AB
SOURCE_QUANTIFIERS: xi in R^2
SOURCE_CONCLUSION: defines omega^0(xi) = lambda_J + A xi and Omega^0_j(xi) = lambda_j + (B xi)_j = lambda_j + (3/(2 pi lambda_j))<b,xi> (j >= 3)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:AB, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:AB | blueprint-W/parts/w7-measure.tex#bpW:w7:omega0@L130-L130 | A and B
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w7-measure.tex#bpW:w7:omega0@L129-L129 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w7:freqcoords
KIND: lemma
TITLE: Frequency coordinates
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:freqcoords@L135-L150
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:freqcoords@L151-L168
CONTRACT_ID: bpW:w7:freqcoords
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W7 standing data (L33-L41): m > 0, lambda_j = sqrt(j^2+m), corrected A, B, max norms on R^2, Leb, ¦k¦ = ¦k_1¦ + ¦k_2¦
SOURCE_QUANTIFIERS: for Borel F subset R^2; xi, xi'
SOURCE_CONCLUSION: (i) A^{-1} = (8pi/21)((-3 lambda_1^2, 4 lambda_1 lambda_2),(4 lambda_1 lambda_2, -3 lambda_2^2)), ¦det A¦ = D_A = 63/(64 pi^2 lambda_1^2 lambda_2^2), A^{-1} b = (8pi/21) lambda_J; (ii) ¦¦A¦¦_infty = N_A < 3/5, ¦¦A^{-1}¦¦_infty = L_A = N_A/D_A; (iii) omega^0 is an affine bijection and Omega^0_j = lambda_j + (4/(7 lambda_j)) s(zeta), s(zeta) = <lambda_J, zeta - lambda_J>; (iv) Leb(omega^0(F)) = D_A Leb(F), diam omega^0(F) <= N_A diam F, ¦xi - xi'¦ <= L_A ¦omega^0(xi) - omega^0(xi')¦
CONSTANT_SCOPE: D_A, N_A, L_A explicit in m
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:omega0, stepW:w7:inverse, stepW:w7:norms, stepW:w7:Omegazeta, stepW:w7:measure-affine, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:omega0 | blueprint-W/parts/w7-measure.tex#bpW:w7:freqcoords@L141-L141 | omega^0, Omega^0
EDGE: stepW:w7:inverse | blueprint-W/parts/w7-measure.tex#bpW:w7:freqcoords@L152-L152 | proof step
EDGE: stepW:w7:norms | blueprint-W/parts/w7-measure.tex#bpW:w7:freqcoords@L158-L158 | proof step
EDGE: stepW:w7:Omegazeta | blueprint-W/parts/w7-measure.tex#bpW:w7:freqcoords@L163-L163 | proof step
EDGE: stepW:w7:measure-affine | blueprint-W/parts/w7-measure.tex#bpW:w7:freqcoords@L166-L166 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w7-measure.tex#bpW:w7:freqcoords@L137-L137 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:inverse
KIND: step
TITLE: Inverse
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:inverse@L152-L157
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:inverse@L152-L157
CONTRACT_ID: stepW:w7:inverse
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:freqcoords: W7 standing data (L33-L41): m > 0, lambda_j = sqrt(j^2+m), corrected A, B, max norms on R^2, Leb, ¦k¦ = ¦k_1¦ + ¦k_2¦
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:freqcoords (for Borel F subset R^2; xi, xi'); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the inverse of A (Sherman-Morrison), A^{-1} b, det A
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:AB, bpW:w0n:nondeg, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:AB | blueprint-W/parts/w7-measure.tex#stepW:w7:inverse@L153-L153 | A = (3/(8pi))(4bb^T - D^2)
EDGE: bpW:w0n:nondeg | blueprint-W/parts/w7-measure.tex#stepW:w7:inverse@L157-L157 | (i) det A
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w7-measure.tex#stepW:w7:inverse@L153-L153 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:norms
KIND: step
TITLE: Norms
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:norms@L158-L162
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:norms@L158-L162
CONTRACT_ID: stepW:w7:norms
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:freqcoords: W7 standing data (L33-L41): m > 0, lambda_j = sqrt(j^2+m), corrected A, B, max norms on R^2, Leb, ¦k¦ = ¦k_1¦ + ¦k_2¦
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:freqcoords (for Borel F subset R^2; xi, xi'); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: N_A < 3/5 and L_A
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#lambda-facts, bpW:w0:basis#lam, stepW:w7:inverse, bpW:w0n:AB
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w7-measure.tex#stepW:w7:norms@L160-L160 | lambda_1 > 1, lambda_2 > 2, lambda increasing
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w7-measure.tex#stepW:w7:norms@L160-L160 | lambda occurs directly here (frozen lam)
EDGE: stepW:w7:inverse | blueprint-W/parts/w7-measure.tex#stepW:w7:norms@L159-L162 | row sums of the displayed inverse computed in the preceding step
EDGE: bpW:w0n:AB | blueprint-W/parts/w7-measure.tex#stepW:w7:norms@L159-L159 | row sums of the corrected A
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:Omegazeta
KIND: step
TITLE: Normal frequencies in $\zeta$
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:Omegazeta@L163-L165
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:Omegazeta@L163-L165
CONTRACT_ID: stepW:w7:Omegazeta
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:freqcoords: W7 standing data (L33-L41): m > 0, lambda_j = sqrt(j^2+m), corrected A, B, max norms on R^2, Leb, ¦k¦ = ¦k_1¦ + ¦k_2¦
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:freqcoords (for Borel F subset R^2; xi, xi'); within the step: zeta; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Omega^0_j in zeta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w7:inverse, bpW:w7:omega0, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w7:inverse | blueprint-W/parts/w7-measure.tex#stepW:w7:Omegazeta@L164-L164 | A^{-1} b
EDGE: bpW:w7:omega0 | blueprint-W/parts/w7-measure.tex#stepW:w7:Omegazeta@L165-L165 | the definition
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w7-measure.tex#stepW:w7:Omegazeta@L164-L164 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:measure-affine
KIND: step
TITLE: Measure and distances
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:measure-affine@L166-L167
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:measure-affine@L166-L167
CONTRACT_ID: stepW:w7:measure-affine
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:freqcoords: W7 standing data (L33-L41): m > 0, lambda_j = sqrt(j^2+m), corrected A, B, max norms on R^2, Leb, ¦k¦ = ¦k_1¦ + ¦k_2¦
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:freqcoords (for Borel F subset R^2; xi, xi'); within the step: F; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iv)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:ext-linear, stepW:w7:norms, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:ext-linear | blueprint-W/parts/w7-measure.tex#stepW:w7:measure-affine@L167-L167 | Lebesgue measure under affine maps
EDGE: stepW:w7:norms | blueprint-W/parts/w7-measure.tex#stepW:w7:measure-affine@L167-L167 | operator norms
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w7-measure.tex#stepW:w7:measure-affine@L167-L167 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w7:unpert-bounds
KIND: lemma
TITLE: Unperturbed separation and asymptotics
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:unpert-bounds@L172-L181
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:unpert-bounds@L182-L204
CONTRACT_ID: bpW:w7:unpert-bounds
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W7 standing data (L33-L41): m > 0, lambda_j = sqrt(j^2+m), corrected A, B, max norms on R^2, Leb, ¦k¦ = ¦k_1¦ + ¦k_2¦; ¦xi¦_infty <= 1/2, zeta = omega^0(xi); beta_* = 1/(2 sqrt(9+m)), a_kappa = m/2 + 1
SOURCE_QUANTIFIERS: for such xi; l in Lambda; i > j >= 3
SOURCE_CONCLUSION: (i) ¦s(zeta)¦ <= 1 and ¦omega^0(xi)¦_infty <= lambda_2 + 3/10; (ii) ¦<l,Omega^0(xi)>¦ >= 3 beta_* <l>; (iii) ¦Omega^0_i - Omega^0_j - (i-j)¦ <= a_kappa (i-j) j^{-2}; (iv) zeta -> <l,Omega^0> affine with Lipschitz constant (4/7)(lambda_1 + lambda_2)¦l¦_{-1}
CONSTANT_SCOPE: beta_*, a_kappa depend only on m
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:freqcoords, bpW:w7:indexdef, stepW:w7:ssize, stepW:w7:plus, stepW:w7:minus, stepW:w7:kappa, stepW:w7:liplOmega, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w7-measure.tex#bpW:w7:unpert-bounds@L173-L175 | zeta and s
EDGE: bpW:w7:indexdef | blueprint-W/parts/w7-measure.tex#bpW:w7:unpert-bounds@L176-L176 | Lambda, <l>, ¦l¦_{-1}
EDGE: stepW:w7:ssize | blueprint-W/parts/w7-measure.tex#bpW:w7:unpert-bounds@L183-L183 | proof step
EDGE: stepW:w7:plus | blueprint-W/parts/w7-measure.tex#bpW:w7:unpert-bounds@L186-L186 | proof step
EDGE: stepW:w7:minus | blueprint-W/parts/w7-measure.tex#bpW:w7:unpert-bounds@L190-L190 | proof step
EDGE: stepW:w7:kappa | blueprint-W/parts/w7-measure.tex#bpW:w7:unpert-bounds@L195-L195 | proof step
EDGE: stepW:w7:liplOmega | blueprint-W/parts/w7-measure.tex#bpW:w7:unpert-bounds@L201-L201 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w7-measure.tex#bpW:w7:unpert-bounds@L175-L175 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:ssize
KIND: step
TITLE: Size of $s$
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:ssize@L183-L185
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:ssize@L183-L185
CONTRACT_ID: stepW:w7:ssize
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:unpert-bounds: W7 standing data (L33-L41): m > 0, lambda_j = sqrt(j^2+m), corrected A, B, max norms on R^2, Leb, ¦k¦ = ¦k_1¦ + ¦k_2¦; ¦xi¦_infty <= 1/2, zeta = omega^0(xi); beta_* = 1/(2 sqrt(9+m)), a_kappa = m/2 + 1
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:unpert-bounds (for such xi; l in Lambda; i > j >= 3); within the step: xi; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦s¦ <= 1 and ¦A xi¦ < 3/10
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:freqcoords, bpW:w0:basis#lam, bpW:w0:basis#lambda-facts
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w7-measure.tex#stepW:w7:ssize@L185-L185 | (ii), (iii)
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w7-measure.tex#stepW:w7:ssize@L184-L184 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w7-measure.tex#stepW:w7:ssize@L184-L184 | lambda_1 > 1 and lambda_2 > 2 give the reciprocal bound
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:plus
KIND: step
TITLE: Plus type
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:plus@L186-L189
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:plus@L186-L189
CONTRACT_ID: stepW:w7:plus
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:unpert-bounds: W7 standing data (L33-L41): m > 0, lambda_j = sqrt(j^2+m), corrected A, B, max norms on R^2, Leb, ¦k¦ = ¦k_1¦ + ¦k_2¦; ¦xi¦_infty <= 1/2, zeta = omega^0(xi); beta_* = 1/(2 sqrt(9+m)), a_kappa = m/2 + 1
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:unpert-bounds (for such xi; l in Lambda; i > j >= 3); within the step: l in Lambda^+; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦<l,Omega^0>¦ >= (8/9)<l> >= 3 beta_* <l>
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w7:ssize, bpW:w0:basis#lambda-facts, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w7:ssize | blueprint-W/parts/w7-measure.tex#stepW:w7:plus@L187-L187 | ¦s¦ <= 1
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w7-measure.tex#stepW:w7:plus@L187-L187 | lambda_j >= j
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w7-measure.tex#stepW:w7:plus@L187-L187 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:minus
KIND: step
TITLE: Minus type
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:minus@L190-L194
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:minus@L190-L194
CONTRACT_ID: stepW:w7:minus
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:unpert-bounds: W7 standing data (L33-L41): m > 0, lambda_j = sqrt(j^2+m), corrected A, B, max norms on R^2, Leb, ¦k¦ = ¦k_1¦ + ¦k_2¦; ¦xi¦_infty <= 1/2, zeta = omega^0(xi); beta_* = 1/(2 sqrt(9+m)), a_kappa = m/2 + 1
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:unpert-bounds (for such xi; l in Lambda; i > j >= 3); within the step: i > j; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Omega^0_i - Omega^0_j >= 3 beta_*(i-j)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w7:ssize, bpW:w0:basis#lambda-facts, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w7:ssize | blueprint-W/parts/w7-measure.tex#stepW:w7:minus@L192-L192 | ¦s¦ <= 1
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w7-measure.tex#stepW:w7:minus@L193-L193 | f' increasing
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w7-measure.tex#stepW:w7:minus@L191-L191 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:kappa
KIND: step
TITLE: Asymptotics
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:kappa@L195-L200
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:kappa@L195-L200
CONTRACT_ID: stepW:w7:kappa
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:unpert-bounds: W7 standing data (L33-L41): m > 0, lambda_j = sqrt(j^2+m), corrected A, B, max norms on R^2, Leb, ¦k¦ = ¦k_1¦ + ¦k_2¦; ¦xi¦_infty <= 1/2, zeta = omega^0(xi); beta_* = 1/(2 sqrt(9+m)), a_kappa = m/2 + 1
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:unpert-bounds (for such xi; l in Lambda; i > j >= 3); within the step: i > j; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the kappa = 2 asymptotics
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#lambda-facts, stepW:w7:ssize, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w7-measure.tex#stepW:w7:kappa@L196-L196 | lambda_n - n = m/(lambda_n + n), f' < 1
EDGE: stepW:w7:ssize | blueprint-W/parts/w7-measure.tex#stepW:w7:kappa@L199-L199 | ¦s¦ <= 1
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w7-measure.tex#stepW:w7:kappa@L196-L196 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:liplOmega
KIND: step
TITLE: Lipschitz
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:liplOmega@L201-L203
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:liplOmega@L201-L203
CONTRACT_ID: stepW:w7:liplOmega
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:unpert-bounds: W7 standing data (L33-L41): m > 0, lambda_j = sqrt(j^2+m), corrected A, B, max norms on R^2, Leb, ¦k¦ = ¦k_1¦ + ¦k_2¦; ¦xi¦_infty <= 1/2, zeta = omega^0(xi); beta_* = 1/(2 sqrt(9+m)), a_kappa = m/2 + 1
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:unpert-bounds (for such xi; l in Lambda; i > j >= 3); within the step: zeta, zeta'; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iv) the Lipschitz bound
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#lam, bpW:w7:freqcoords
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w7-measure.tex#stepW:w7:liplOmega@L202-L202 | lambda occurs directly here (frozen lam)
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w7-measure.tex#stepW:w7:liplOmega@L202-L203 | the affine Omega^0 formula and s(zeta) from (iii)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w7:constdef
KIND: definition
TITLE: W7 constants
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:constdef@L211-L231
PROOF_SOURCE: -
CONTRACT_ID: bpW:w7:constdef
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W7 standing data (L33-L41): m > 0, lambda_j = sqrt(j^2+m), corrected A, B, max norms on R^2, Leb, ¦k¦ = ¦k_1¦ + ¦k_2¦; m > 0
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: defines in order (C1) tau = 24, varpi = 1/2, beta = 1/4, w = 1/47; (C2) lambda_1, lambda_2, D_A, N_A, L_A, beta_*, a_kappa, W = lambda_2 + 1, vartheta = beta_*/W, c_Lambda = (4/7)(lambda_1 + lambda_2) + 1, K_* = 16 c_Lambda, j_* = (16 c_Lambda)^2; (C3) X, N_X, sigma_X, c_X; (C4) theta_0 and alpha_0; (C5) C_P, C_I, C_7 = L_A(C_P + C_I); (C6) per application Pi, alpha in (0,alpha_0], hat alpha = alpha^{44/47}, check alpha = alpha^{48/47}; every constant of (C1)-(C5) depends on m only
CONSTANT_SCOPE: (C1)-(C5) depend on m only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:freqcoords, bpW:w7:unpert-bounds, bpW:w7:Xdef, bpW:w7:Xzones#consts, bpW:w7:ext-zeta, bpW:w0:basis#lam, bpW:w7:constdef#base
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w7-measure.tex#bpW:w7:constdef@L215-L215 | D_A, N_A, L_A
EDGE: bpW:w7:unpert-bounds | blueprint-W/parts/w7-measure.tex#bpW:w7:constdef@L216-L216 | beta_*, a_kappa
EDGE: bpW:w7:Xdef | blueprint-W/parts/w7-measure.tex#bpW:w7:constdef@L218-L218 | X
EDGE: bpW:w7:Xzones#consts | blueprint-W/parts/w7-measure.tex#bpW:w7:constdef@L219-L219 | sigma_X, c_X (defined in the statement of Lemma bpW:w7:Xzones)
EDGE: bpW:w7:ext-zeta | blueprint-W/parts/w7-measure.tex#bpW:w7:constdef@L225-L225 | Z_3
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w7-measure.tex#bpW:w7:constdef@L215-L215 | lambda occurs directly here (frozen lam)
EDGE: bpW:w7:constdef#base | blueprint-W/parts/w7-measure.tex#bpW:w7:constdef@L214-L217 | the preliminary constants (C1)-(C2), defined before X
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The (C1)-(C2) definition is also represented by bpW:w7:constdef#base so that X and the exceptional affine constants can depend on it without depending on (C3)-(C6). No positivity assertion is added to the base definition.

NODE: bpW:w7:zones
KIND: definition
TITLE: Resonance zones
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:zones@L255-L264
PROOF_SOURCE: -
CONTRACT_ID: bpW:w7:zones
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Pi subset {¦xi¦_infty <= 1/2} Borel, 0 < alpha <= alpha_0
SOURCE_QUANTIFIERS: (k,l) in Z; D, omega', Omega'_j, a > 0
SOURCE_CONCLUSION: defines (i) the preparatory zones S_kl = {xi in Pi : ¦<k,omega^0> + <l,Omega^0>¦ < hat alpha hat w(l)/A_k} and Xi = union S_kl; (ii) zones R_kl(a) = {xi in D : ¦<k,omega'> + <l,Omega'>¦ < a <l>/A_k} for maps omega', Omega' on a Borel D subset Pi
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:constdef, bpW:w7:omega0, bpW:w7:indexdef
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:constdef | blueprint-W/parts/w7-measure.tex#bpW:w7:zones@L256-L256 | alpha_0, hat alpha
EDGE: bpW:w7:omega0 | blueprint-W/parts/w7-measure.tex#bpW:w7:zones@L259-L259 | omega^0, Omega^0
EDGE: bpW:w7:indexdef | blueprint-W/parts/w7-measure.tex#bpW:w7:zones@L259-L259 | Z, A_k, hat w, <l>
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w7:family
KIND: definition
TITLE: Admissible frequency family
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:family@L266-L280
PROOF_SOURCE: -
CONTRACT_ID: bpW:w7:family
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Pi, alpha as in Definition bpW:w7:zones
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: defines an admissible family (D_nu,omega_nu,Omega_nu,K_nu)_{nu>=0}: D_nu subset Pi Borel, K_nu >= 2^nu, K_{-1} = 0, numbers eps_omega, eps_1, eps_2 in [0,alpha], theta in [0,theta_0] with (H1) ¦omega_nu - omega^0¦ <= eps_omega and Lipschitz theta; (H2) ¦Omega_{nu,j} - Omega^0_j¦ <= eps_1 j^{-1} + eps_2 j^{-1/2} and Lipschitz theta j^{-1/2}; its iteration zones R^nu_kl = R_kl(check alpha) and the excluded set E = Xi cup union R^nu_kl (¦k¦ > K_{nu-1})
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:zones, bpW:w7:constdef, bpW:w7:omega0
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:zones | blueprint-W/parts/w7-measure.tex#bpW:w7:family@L277-L277 | Xi and R_kl
EDGE: bpW:w7:constdef | blueprint-W/parts/w7-measure.tex#bpW:w7:family@L269-L269 | theta_0, check alpha
EDGE: bpW:w7:omega0 | blueprint-W/parts/w7-measure.tex#bpW:w7:family@L272-L272 | omega^0, Omega^0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w7:slab
KIND: lemma
TITLE: Slicing
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:slab@L317-L322
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:slab@L323-L334
CONTRACT_ID: bpW:w7:slab
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E subset R^2 Borel, nonempty, diam_infty E <= rho; phi : E -> R continuous on E; i in {1,2}, sigma > 0 with ¦phi(zeta + t e_i) - phi(zeta)¦ >= sigma ¦t¦ whenever zeta, zeta + t e_i in E
SOURCE_QUANTIFIERS: for every eta > 0
SOURCE_CONCLUSION: {zeta in E : ¦phi(zeta)¦ < eta} is Borel with measure <= 2 eta rho/sigma
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w7:slab-borel, stepW:w7:slab-line, stepW:w7:slab-int
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w7:slab-borel | blueprint-W/parts/w7-measure.tex#bpW:w7:slab@L324-L324 | proof step
EDGE: stepW:w7:slab-line | blueprint-W/parts/w7-measure.tex#bpW:w7:slab@L326-L326 | proof step
EDGE: stepW:w7:slab-int | blueprint-W/parts/w7-measure.tex#bpW:w7:slab@L330-L330 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:slab-borel
KIND: step
TITLE: Borel
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:slab-borel@L324-L325
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:slab-borel@L324-L325
CONTRACT_ID: stepW:w7:slab-borel
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:slab: E subset R^2 Borel, nonempty, diam_infty E <= rho; phi : E -> R continuous on E; i in {1,2}, sigma > 0 with ¦phi(zeta + t e_i) - phi(zeta)¦ >= sigma ¦t¦ whenever zeta, zeta + t e_i in E
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:slab (for every eta > 0); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the set is Borel
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:ext-borel
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:ext-borel | blueprint-W/parts/w7-measure.tex#stepW:w7:slab-borel@L325-L325 | Borel sets
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:slab-line
KIND: step
TITLE: One line
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:slab-line@L326-L329
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:slab-line@L326-L329
CONTRACT_ID: stepW:w7:slab-line
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:slab: E subset R^2 Borel, nonempty, diam_infty E <= rho; phi : E -> R continuous on E; i in {1,2}, sigma > 0 with ¦phi(zeta + t e_i) - phi(zeta)¦ >= sigma ¦t¦ whenever zeta, zeta + t e_i in E
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:slab (for every eta > 0); within the step: y; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Leb_1(T_y) <= 2 eta/sigma
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:ext-diam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:ext-diam | blueprint-W/parts/w7-measure.tex#stepW:w7:slab-line@L329-L329 | small diameter
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:slab-int
KIND: step
TITLE: Integrate
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:slab-int@L330-L333
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:slab-int@L330-L333
CONTRACT_ID: stepW:w7:slab-int
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:slab: E subset R^2 Borel, nonempty, diam_infty E <= rho; phi : E -> R continuous on E; i in {1,2}, sigma > 0 with ¦phi(zeta + t e_i) - phi(zeta)¦ >= sigma ¦t¦ whenever zeta, zeta + t e_i in E
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:slab (for every eta > 0); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: integrating gives <= 2 eta rho/sigma
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:ext-tonelli, stepW:w7:slab-line
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:ext-tonelli | blueprint-W/parts/w7-measure.tex#stepW:w7:slab-int@L332-L332 | Tonelli
EDGE: stepW:w7:slab-line | blueprint-W/parts/w7-measure.tex#stepW:w7:slab-int@L333-L333 | one line
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w7:sep
KIND: lemma
TITLE: Normal separation; Melnikov conditions with $k=0$
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:sep@L345-L348
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:sep@L349-L356
CONTRACT_ID: bpW:w7:sep
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta, frequency pairs, phi_kl
SOURCE_QUANTIFIERS: for a frequency pair on D and l in Lambda
SOURCE_CONCLUSION: ¦<l,Omega'(xi)>¦ >= 2 beta_* <l> on D; in particular ¦<l,Omega'>¦ >= a<l>/A_0 for a <= 2 beta_*, and R_{0l}(a) = S_{0l} = empty
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:basic#data, stepW:w7:sep-drift, stepW:w7:sep-concl
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:basic#data | blueprint-W/parts/w7-measure.tex#bpW:w7:sep@L346-L346 | frequency pairs
EDGE: stepW:w7:sep-drift | blueprint-W/parts/w7-measure.tex#bpW:w7:sep@L350-L350 | proof step
EDGE: stepW:w7:sep-concl | blueprint-W/parts/w7-measure.tex#bpW:w7:sep@L353-L353 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:sep-drift
KIND: step
TITLE: Drift
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:sep-drift@L350-L352
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:sep-drift@L350-L352
CONTRACT_ID: stepW:w7:sep-drift
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:sep: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta, frequency pairs, phi_kl
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:sep (for a frequency pair on D and l in Lambda); within the step: l; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦<l,Omega' - Omega^0>¦ <= 4 alpha <= beta_* <l>
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:family, bpW:w7:constdef
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:family | blueprint-W/parts/w7-measure.tex#stepW:w7:sep-drift@L351-L351 | (H2)
EDGE: bpW:w7:constdef | blueprint-W/parts/w7-measure.tex#stepW:w7:sep-drift@L352-L352 | (C4)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:sep-concl
KIND: step
TITLE: Conclude
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:sep-concl@L353-L355
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:sep-concl@L353-L355
CONTRACT_ID: stepW:w7:sep-concl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:sep: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta, frequency pairs, phi_kl
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:sep (for a frequency pair on D and l in Lambda); within the step: l; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the separation; S_{0l}, R_{0l} empty
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:unpert-bounds, stepW:w7:sep-drift, bpW:w7:zones, bpW:w7:indexdef, bpW:w7:constdef
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:unpert-bounds | blueprint-W/parts/w7-measure.tex#stepW:w7:sep-concl@L354-L354 | (ii)
EDGE: stepW:w7:sep-drift | blueprint-W/parts/w7-measure.tex#stepW:w7:sep-concl@L354-L354 | the drift
EDGE: bpW:w7:zones | blueprint-W/parts/w7-measure.tex#stepW:w7:sep-concl@L354-L355 | S_0l and R_0l are the strict-inequality zones
EDGE: bpW:w7:indexdef | blueprint-W/parts/w7-measure.tex#stepW:w7:sep-concl@L355-L355 | hat w(l) <= <l> and A_0 = 1
EDGE: bpW:w7:constdef | blueprint-W/parts/w7-measure.tex#stepW:w7:sep-concl@L354-L355 | hat alpha and check alpha <= beta_*
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w7:largek
KIND: lemma
TITLE: Nonempty zones have large $\abs k$
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:largek@L359-L363
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:largek@L364-L371
CONTRACT_ID: bpW:w7:largek
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta, frequency pairs, phi_kl; l in Lambda, a <= beta_*
SOURCE_QUANTIFIERS: for a frequency pair on D
SOURCE_CONCLUSION: if {xi in D : ¦phi_kl(xi)¦ < a<l>/A_k} is nonempty then ¦k¦ >= vartheta <l>, in particular k != 0; likewise for S_kl (a = hat alpha)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:basic#data, stepW:w7:largek-tan, stepW:w7:largek-cmp, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:basic#data | blueprint-W/parts/w7-measure.tex#bpW:w7:largek@L360-L360 | frequency pairs, phi_kl
EDGE: stepW:w7:largek-tan | blueprint-W/parts/w7-measure.tex#bpW:w7:largek@L365-L365 | proof step
EDGE: stepW:w7:largek-cmp | blueprint-W/parts/w7-measure.tex#bpW:w7:largek@L368-L368 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w7-measure.tex#bpW:w7:largek@L366-L366 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:largek-tan
KIND: step
TITLE: Bound the tangential term
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:largek-tan@L365-L367
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:largek-tan@L365-L367
CONTRACT_ID: stepW:w7:largek-tan
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:largek: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta, frequency pairs, phi_kl; l in Lambda, a <= beta_*; the enclosing implication premise {xi in D : ¦phi_kl(xi)¦ < a <l>/A_k} is nonempty
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:largek (for a frequency pair on D); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦<k,omega'>¦ <= W¦k¦
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:unpert-bounds, bpW:w7:family, bpW:w0:basis#lam, bpW:w7:constdef
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:unpert-bounds | blueprint-W/parts/w7-measure.tex#stepW:w7:largek-tan@L366-L366 | (i)
EDGE: bpW:w7:family | blueprint-W/parts/w7-measure.tex#stepW:w7:largek-tan@L366-L366 | (H1)
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w7-measure.tex#stepW:w7:largek-tan@L366-L366 | lambda occurs directly here (frozen lam)
EDGE: bpW:w7:constdef | blueprint-W/parts/w7-measure.tex#stepW:w7:largek-tan@L366-L366 | W = lambda_2 + 1 and alpha <= alpha_0
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:largek-cmp
KIND: step
TITLE: Compare
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:largek-cmp@L368-L370
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:largek-cmp@L368-L370
CONTRACT_ID: stepW:w7:largek-cmp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:largek: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta, frequency pairs, phi_kl; l in Lambda, a <= beta_*; the enclosing implication premise {xi in D : ¦phi_kl(xi)¦ < a <l>/A_k} is nonempty
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:largek (for a frequency pair on D); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: W¦k¦ >= beta_* <l>
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:sep, stepW:w7:largek-tan
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:sep | blueprint-W/parts/w7-measure.tex#stepW:w7:largek-cmp@L370-L370 | separation
EDGE: stepW:w7:largek-tan | blueprint-W/parts/w7-measure.tex#stepW:w7:largek-cmp@L369-L369 | the tangential bound
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w7:zone
KIND: lemma
TITLE: Zone estimate
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:zone@L374-L380
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:zone@L381-L394
CONTRACT_ID: bpW:w7:zone
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta, frequency pairs, phi_kl; k != 0; psi : D -> R with ¦psi(xi) - psi(xi')¦ <= (¦k¦/8)¦omega^0(xi) - omega^0(xi')¦
SOURCE_QUANTIFIERS: for eta > 0
SOURCE_CONCLUSION: Leb{xi in D : ¦<k,omega'(xi)> + psi(xi)¦ < eta} <= 8 eta rho_zeta/(¦k¦ D_A); this applies to psi = <l,Omega'> when l = 0 or l in Lambda with ¦k¦ >= 8 c_Lambda ¦l¦_{-1/2}, and to constants
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:basic#data, stepW:w7:zone-lower, stepW:w7:zone-slab, stepW:w7:zone-psi, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:basic#data | blueprint-W/parts/w7-measure.tex#bpW:w7:zone@L375-L375 | frequency pairs, rho_zeta
EDGE: stepW:w7:zone-lower | blueprint-W/parts/w7-measure.tex#bpW:w7:zone@L382-L382 | proof step
EDGE: stepW:w7:zone-slab | blueprint-W/parts/w7-measure.tex#bpW:w7:zone@L387-L387 | proof step
EDGE: stepW:w7:zone-psi | blueprint-W/parts/w7-measure.tex#bpW:w7:zone@L390-L390 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w7-measure.tex#bpW:w7:zone@L392-L392 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:zone-lower
KIND: step
TITLE: Lower Lipschitz bound in $\zeta$
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:zone-lower@L382-L386
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:zone-lower@L382-L386
CONTRACT_ID: stepW:w7:zone-lower
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:zone: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta, frequency pairs, phi_kl; k != 0; psi : D -> R with ¦psi(xi) - psi(xi')¦ <= (¦k¦/8)¦omega^0(xi) - omega^0(xi')¦
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:zone (for eta > 0); within the step: zeta; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦phi(zeta + t e_i) - phi(zeta)¦ >= (¦k¦/4)¦t¦
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:family, bpW:w7:freqcoords, bpW:w7:constdef
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:family | blueprint-W/parts/w7-measure.tex#stepW:w7:zone-lower@L385-L385 | (H1)
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w7-measure.tex#stepW:w7:zone-lower@L385-L385 | (iv)
EDGE: bpW:w7:constdef | blueprint-W/parts/w7-measure.tex#stepW:w7:zone-lower@L385-L385 | theta_0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:zone-slab
KIND: step
TITLE: Slicing
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:zone-slab@L387-L389
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:zone-slab@L387-L389
CONTRACT_ID: stepW:w7:zone-slab
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:zone: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta, frequency pairs, phi_kl; k != 0; psi : D -> R with ¦psi(xi) - psi(xi')¦ <= (¦k¦/8)¦omega^0(xi) - omega^0(xi')¦
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:zone (for eta > 0); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the measure bound via slicing
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:slab, bpW:w7:freqcoords, stepW:w7:zone-lower
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:slab | blueprint-W/parts/w7-measure.tex#stepW:w7:zone-slab@L388-L388 | slicing
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w7-measure.tex#stepW:w7:zone-slab@L389-L389 | (iv)
EDGE: stepW:w7:zone-lower | blueprint-W/parts/w7-measure.tex#stepW:w7:zone-slab@L388-L388 | sigma = ¦k¦/4
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:zone-psi
KIND: step
TITLE: The admissible $\psi$
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:zone-psi@L390-L393
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:zone-psi@L390-L393
CONTRACT_ID: stepW:w7:zone-psi
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:zone: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta, frequency pairs, phi_kl; k != 0; psi : D -> R with ¦psi(xi) - psi(xi')¦ <= (¦k¦/8)¦omega^0(xi) - omega^0(xi')¦
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:zone (for eta > 0); within the step: l; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the admissible psi
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:unpert-bounds, bpW:w7:family, bpW:w7:constdef, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:unpert-bounds | blueprint-W/parts/w7-measure.tex#stepW:w7:zone-psi@L391-L391 | (iv)
EDGE: bpW:w7:family | blueprint-W/parts/w7-measure.tex#stepW:w7:zone-psi@L391-L391 | (H2)
EDGE: bpW:w7:constdef | blueprint-W/parts/w7-measure.tex#stepW:w7:zone-psi@L392-L392 | c_Lambda
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w7-measure.tex#stepW:w7:zone-psi@L392-L392 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w7:Xdef
KIND: definition
TITLE: Exceptional set
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:Xdef@L398-L401
PROOF_SOURCE: -
CONTRACT_ID: bpW:w7:Xdef
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W7 standing data (L33-L41): m > 0, lambda_j = sqrt(j^2+m), corrected A, B, max norms on R^2, Leb, ¦k¦ = ¦k_1¦ + ¦k_2¦; the constants K_*, vartheta, j_* of (C2)
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: defines X = {(k,l) in Z^2 x Lambda : 1 <= ¦k¦ < K_*, <l> < K_*/vartheta, and l in Lambda^+ or l = +-(e_i - e_j) with i > j, j < j_*}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:indexdef, bpW:w7:constdef#base
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:indexdef | blueprint-W/parts/w7-measure.tex#bpW:w7:Xdef@L399-L399 | Lambda^+-, <l>
EDGE: bpW:w7:constdef#base | blueprint-W/parts/w7-measure.tex#bpW:w7:Xdef@L399-L400 | the constants K_*, vartheta and j_* from (C2)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w7:dichotomy
KIND: lemma
TITLE: Dichotomy
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:dichotomy@L403-L406
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:dichotomy@L407-L417
CONTRACT_ID: bpW:w7:dichotomy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta, frequency pairs, phi_kl
SOURCE_QUANTIFIERS: (k,l) in Z minus X, l in Lambda
SOURCE_CONCLUSION: X is finite; if a zone of Lemma bpW:w7:largek for (k,l) is nonempty then k != 0, <l> <= ¦k¦/vartheta and ¦k¦ >= 8 c_Lambda ¦l¦_{-1/2}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:Xdef, stepW:w7:Xfinite, stepW:w7:dich-large, stepW:w7:dich-small, bpW:w7:basic#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:Xdef | blueprint-W/parts/w7-measure.tex#bpW:w7:dichotomy@L404-L404 | X
EDGE: stepW:w7:Xfinite | blueprint-W/parts/w7-measure.tex#bpW:w7:dichotomy@L408-L408 | proof step
EDGE: stepW:w7:dich-large | blueprint-W/parts/w7-measure.tex#bpW:w7:dichotomy@L411-L411 | proof step
EDGE: stepW:w7:dich-small | blueprint-W/parts/w7-measure.tex#bpW:w7:dichotomy@L414-L414 | proof step
EDGE: bpW:w7:basic#data | blueprint-W/parts/w7-measure.tex#bpW:w7:dichotomy@L404-L405 | the fixed frequency pair and zone setting
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:Xfinite
KIND: step
TITLE: Finite
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:Xfinite@L408-L410
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:Xfinite@L408-L410
CONTRACT_ID: stepW:w7:Xfinite
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:dichotomy: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta, frequency pairs, phi_kl
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:dichotomy ((k,l) in Z minus X, l in Lambda); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: X is finite
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:indexdef, bpW:w7:Xdef
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:indexdef | blueprint-W/parts/w7-measure.tex#stepW:w7:Xfinite@L409-L409 | <l> on Lambda^+
EDGE: bpW:w7:Xdef | blueprint-W/parts/w7-measure.tex#stepW:w7:Xfinite@L409-L410 | the support and index cutoffs defining X
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:dich-large
KIND: step
TITLE: Large $k$
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:dich-large@L411-L413
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:dich-large@L411-L413
CONTRACT_ID: stepW:w7:dich-large
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:dichotomy: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta, frequency pairs, phi_kl; (k,l) in Z minus X, l in Lambda, and the zone of largek is nonempty; the case condition on ¦k¦ is as stated in this step
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:dichotomy ((k,l) in Z minus X, l in Lambda); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: k != 0, <l> <= ¦k¦/vartheta, and the ¦k¦ bound when ¦k¦ >= K_*
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:largek, bpW:w7:constdef
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:largek | blueprint-W/parts/w7-measure.tex#stepW:w7:dich-large@L412-L412 | large k
EDGE: bpW:w7:constdef | blueprint-W/parts/w7-measure.tex#stepW:w7:dich-large@L412-L412 | K_* = 16 c_Lambda
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:dich-small
KIND: step
TITLE: Small $k$
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:dich-small@L414-L416
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:dich-small@L414-L416
CONTRACT_ID: stepW:w7:dich-small
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:dichotomy: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta, frequency pairs, phi_kl; (k,l) in Z minus X, l in Lambda, and the zone of largek is nonempty; the case condition on ¦k¦ is as stated in this step
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:dichotomy ((k,l) in Z minus X, l in Lambda); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: for ¦k¦ < K_*, (k,l) not in X forces l in Lambda^- with j >= j_*, whence the ¦k¦ bound
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:constdef, bpW:w7:Xdef, stepW:w7:dich-large
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:constdef | blueprint-W/parts/w7-measure.tex#stepW:w7:dich-small@L416-L416 | j_*
EDGE: bpW:w7:Xdef | blueprint-W/parts/w7-measure.tex#stepW:w7:dich-small@L415-L415 | not in X forces a difference with j >= j_*
EDGE: stepW:w7:dich-large | blueprint-W/parts/w7-measure.tex#stepW:w7:dich-small@L415-L416 | largek supplies k != 0 and <l> <= ¦k¦/vartheta
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w7:Xzones
KIND: lemma
TITLE: Exceptional zones
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:Xzones@L421-L429
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:Xzones@L430-L444
CONTRACT_ID: bpW:w7:Xzones
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta, frequency pairs, phi_kl; for (k,l) in X, g_kl(zeta) = <k,zeta> + <l,Omega^0(zeta)> = c_kl + <p_kl,zeta>, p_kl = k + (4/7)(sum l_j/lambda_j) lambda_J; sigma_X, c_X as displayed
SOURCE_QUANTIFIERS: for a frequency pair on D, (k,l) in X, 0 < a <= hat alpha
SOURCE_CONCLUSION: g_kl is not identically 0; sigma_X, c_X > 0; the zone Y = {xi in D : ¦phi_kl¦ < a<l>/A_k} is empty if p_kl = 0 and Leb(Y) <= 4 rho_zeta a K_*/(vartheta sigma_X D_A) if p_kl != 0
CONSTANT_SCOPE: sigma_X, c_X depend only on m
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:Xdef, bpW:w7:freqcoords, bpW:w7:Xzones#consts, stepW:w7:X-A3, stepW:w7:X-const, stepW:w7:X-slope, bpW:w0:basis#lam, bpW:w7:basic#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:Xdef | blueprint-W/parts/w7-measure.tex#bpW:w7:Xzones@L422-L422 | X
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w7-measure.tex#bpW:w7:Xzones@L423-L423 | (iii)
EDGE: bpW:w7:Xzones#consts | blueprint-W/parts/w7-measure.tex#bpW:w7:Xzones@L424-L424 | sigma_X, c_X
EDGE: stepW:w7:X-A3 | blueprint-W/parts/w7-measure.tex#bpW:w7:Xzones@L431-L431 | proof step
EDGE: stepW:w7:X-const | blueprint-W/parts/w7-measure.tex#bpW:w7:Xzones@L436-L436 | proof step
EDGE: stepW:w7:X-slope | blueprint-W/parts/w7-measure.tex#bpW:w7:Xzones@L439-L439 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w7-measure.tex#bpW:w7:Xzones@L423-L423 | lambda occurs directly here (frozen lam)
EDGE: bpW:w7:basic#data | blueprint-W/parts/w7-measure.tex#bpW:w7:Xzones@L426-L428 | the frequency pair on D, phi_kl and rho_zeta
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:X-A3
KIND: step
TITLE: Nondegeneracy
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:X-A3@L431-L435
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:X-A3@L431-L435
CONTRACT_ID: stepW:w7:X-A3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:Xzones: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta, frequency pairs, phi_kl; for (k,l) in X, g_kl(zeta) = <k,zeta> + <l,Omega^0(zeta)> = c_kl + <p_kl,zeta>, p_kl = k + (4/7)(sum l_j/lambda_j) lambda_J; sigma_X, c_X as displayed
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:Xzones (for a frequency pair on D, (k,l) in X, 0 < a <= hat alpha); within the step: (k,l) in X; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: g_kl not identically zero; constant case value nonzero; sigma_X, c_X > 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:nondeg, bpW:w7:freqcoords, bpW:w0:basis#lam, stepW:w7:Xfinite, bpW:w7:Xzones#consts
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:nondeg | blueprint-W/parts/w7-measure.tex#stepW:w7:X-A3@L433-L433 | (iii) (A3)
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w7-measure.tex#stepW:w7:X-A3@L434-L434 | omega^0 bijective
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w7-measure.tex#stepW:w7:X-A3@L434-L434 | lambda occurs directly here (frozen lam)
EDGE: stepW:w7:Xfinite | blueprint-W/parts/w7-measure.tex#stepW:w7:X-A3@L435-L435 | X is finite, used to obtain positive minima
EDGE: bpW:w7:Xzones#consts | blueprint-W/parts/w7-measure.tex#stepW:w7:X-A3@L434-L435 | the defined g_kl, sigma_X and c_X
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:X-const
KIND: step
TITLE: Constant case
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:X-const@L436-L438
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:X-const@L436-L438
CONTRACT_ID: stepW:w7:X-const
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:Xzones: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta, frequency pairs, phi_kl; for (k,l) in X, g_kl(zeta) = <k,zeta> + <l,Omega^0(zeta)> = c_kl + <p_kl,zeta>, p_kl = k + (4/7)(sum l_j/lambda_j) lambda_J; sigma_X, c_X as displayed; local case premise p_kl = 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:Xzones (for a frequency pair on D, (k,l) in X, 0 < a <= hat alpha); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Y is empty when p_kl = 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:family, bpW:w7:constdef, stepW:w7:X-A3, bpW:w7:Xdef
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:family | blueprint-W/parts/w7-measure.tex#stepW:w7:X-const@L437-L437 | (H1), (H2)
EDGE: bpW:w7:constdef | blueprint-W/parts/w7-measure.tex#stepW:w7:X-const@L438-L438 | (C4)
EDGE: stepW:w7:X-A3 | blueprint-W/parts/w7-measure.tex#stepW:w7:X-const@L437-L437 | c_X
EDGE: bpW:w7:Xdef | blueprint-W/parts/w7-measure.tex#stepW:w7:X-const@L437-L438 | the exceptional-set cutoffs used in the two inequalities
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w7:X-slope
KIND: step
TITLE: Sloped case
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:X-slope@L439-L443
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:X-slope@L439-L443
CONTRACT_ID: stepW:w7:X-slope
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:Xzones: the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta, frequency pairs, phi_kl; for (k,l) in X, g_kl(zeta) = <k,zeta> + <l,Omega^0(zeta)> = c_kl + <p_kl,zeta>, p_kl = k + (4/7)(sum l_j/lambda_j) lambda_J; sigma_X, c_X as displayed; local case premise p_kl != 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:Xzones (for a frequency pair on D, (k,l) in X, 0 < a <= hat alpha); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the measure bound when p_kl != 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:family, bpW:w7:constdef, bpW:w7:slab, bpW:w7:freqcoords, stepW:w7:X-A3, bpW:w7:Xdef
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:family | blueprint-W/parts/w7-measure.tex#stepW:w7:X-slope@L441-L441 | (H1)-(H2)
EDGE: bpW:w7:constdef | blueprint-W/parts/w7-measure.tex#stepW:w7:X-slope@L441-L441 | (C4)
EDGE: bpW:w7:slab | blueprint-W/parts/w7-measure.tex#stepW:w7:X-slope@L442-L442 | slicing
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w7-measure.tex#stepW:w7:X-slope@L443-L443 | (iv)
EDGE: stepW:w7:X-A3 | blueprint-W/parts/w7-measure.tex#stepW:w7:X-slope@L440-L442 | sigma_X > 0 discharges the positive-slope premise of slab
EDGE: bpW:w7:Xdef | blueprint-W/parts/w7-measure.tex#stepW:w7:X-slope@L441-L442 | the bounds on ¦k¦ and <l> for (k,l) in X
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w7:count
KIND: lemma
TITLE: Counting
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:count@L449-L452
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:count@L453-L457
CONTRACT_ID: bpW:w7:count
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: N >= 1; k != 0
SOURCE_CONCLUSION: (i) #{l in Lambda^+ : <l> <= N} <= 4N^2; (ii) if K_nu >= 2^nu and K_{-1} = 0 then #{nu >= 0 : ¦k¦ > K_{nu-1}} <= ¦k¦; (iii) sum_{k != 0} ¦k¦^{-3} = Z_3 < 7
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:indexdef, bpW:w7:ext-zeta
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:indexdef | blueprint-W/parts/w7-measure.tex#bpW:w7:count@L450-L450 | Lambda^+ and <l>
EDGE: bpW:w7:ext-zeta | blueprint-W/parts/w7-measure.tex#bpW:w7:count@L456-L456 | (iii)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Inline proof (L454-L456).

NODE: bpW:w7#data
KIND: definition
TITLE: W7 standing data
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7@L33-L41
PROOF_SOURCE: -
CONTRACT_ID: bpW:w7#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: Standing assumption m > 0 and the conventions of W0: lambda_j = sqrt(j^2+m), I_j = ¦z_j¦^2, period-one angles, corrected A, B (printed P96-W values not used); max norm ¦.¦_infty on R^2, induced operator norm (maximal row sum); Leb = volume on Fin 2 -> R; ¦k¦ = ¦k_1¦ + ¦k_2¦ (the norm of KAM.IsDiophantine); diam_infty; tangential modes J = {1,2} (Fin 2 index i is mode i+1), normal modes j >= 3
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:mass, bpW:w0:basis#lam, bpW:w0:periodone#linearTorus, bpW:w0n:AB, bpW:wh:dioph#IsDiophantine
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:mass | blueprint-W/parts/w7-measure.tex#bpW:w7@L33-L33 | standing assumption m > 0
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w7-measure.tex#bpW:w7@L34-L34 | lambda_j
EDGE: bpW:w0:periodone#linearTorus | blueprint-W/parts/w7-measure.tex#bpW:w7@L35-L35 | period-one convention
EDGE: bpW:w0n:AB | blueprint-W/parts/w7-measure.tex#bpW:w7@L35-L35 | the corrected A, B
EDGE: bpW:wh:dioph#IsDiophantine | blueprint-W/parts/w7-measure.tex#bpW:w7@L39-L39 | the norm ¦k¦ of KAM.IsDiophantine
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Unlabelled 'Standing data' paragraph (SPEC hypothesis packages).

NODE: bpW:w7:basic#data
KIND: definition
TITLE: Fixed data for the zone estimates
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:basic@L339-L343
PROOF_SOURCE: -
CONTRACT_ID: bpW:w7:basic#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Pi, alpha in (0,alpha_0], an admissible family
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: fixes Pi, alpha, an admissible family; rho = diam_infty Pi, rho_zeta = diam_infty omega^0(Pi) <= N_A rho; a frequency pair on Borel D subset Pi is (omega^0,Omega^0) (eps's and theta = 0) or some (omega_nu,Omega_nu) on D_nu; phi_kl = <k,omega'> + <l,Omega'> as a function of zeta in omega^0(D)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:family, bpW:w7:freqcoords
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:family | blueprint-W/parts/w7-measure.tex#bpW:w7:basic@L339-L339 | admissible family
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w7-measure.tex#bpW:w7:basic@L340-L340 | N_A, omega^0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Unlabelled prose L339-L343 fixing the data of the zone lemmas (SPEC section-data rule).

NODE: bpW:w7:Xzones#consts
KIND: definition
TITLE: The exceptional-zone constants sigma_X, c_X
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:Xzones@L422-L426
PROOF_SOURCE: -
CONTRACT_ID: bpW:w7:Xzones#consts
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0; X (Definition bpW:w7:Xdef)
SOURCE_QUANTIFIERS: (k,l) in X
SOURCE_CONCLUSION: defines g_kl(zeta) = <k,zeta> + <l,Omega^0(zeta)> = c_kl + <p_kl,zeta> with p_kl = k + (4/7)(sum_j l_j/lambda_j) lambda_J, sigma_X = min{¦p_kl¦_infty : (k,l) in X, p_kl != 0} and c_X = min{¦<k,lambda_J> + <l,lambda>¦ : (k,l) in X, p_kl = 0} (minimum over the empty set := 1)
CONSTANT_SCOPE: depend on m only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:Xdef, bpW:w7:freqcoords, bpW:w7:omega0, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:Xdef | blueprint-W/parts/w7-measure.tex#bpW:w7:Xzones@L422-L422 | X
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w7-measure.tex#bpW:w7:Xzones@L423-L423 | (iii) affine Omega^0
EDGE: bpW:w7:omega0 | blueprint-W/parts/w7-measure.tex#bpW:w7:Xzones@L422-L422 | Omega^0
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w7-measure.tex#bpW:w7:Xzones@L423-L423 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w7a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Definitional part of Lemma bpW:w7:Xzones, split off so that Definition bpW:w7:constdef (C3) can use sigma_X, c_X without depending on the lemma, whose proof uses (C4) (otherwise a dependency cycle).

NODE: bpW:w7:constdef#base
KIND: definition
TITLE: Preliminary W7 constants (C1)-(C2)
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#bpW:w7:constdef@L214-L217
PROOF_SOURCE: -
CONTRACT_ID: bpW:w7:constdef#base
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0; W7 standing data; corrected A and B
SOURCE_QUANTIFIERS: m fixed before all application data Pi, alpha and frequency families
SOURCE_CONCLUSION: defines tau = 24, varpi = 1/2, beta = 1/4, w = beta/(4 kappa+4-beta) = 1/47 (kappa = 2); lambda_1,lambda_2; D_A,N_A,L_A of freqcoords; beta_* = 1/(2 sqrt(9+m)), a_kappa = m/2+1; W = lambda_2+1; vartheta = beta_*/W; c_Lambda = (4/7)(lambda_1+lambda_2)+1; K_* = 16 c_Lambda; j_* = (16 c_Lambda)^2
CONSTANT_SCOPE: all depend on m only; independent of Pi,alpha and the frequency families
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:freqcoords, bpW:w7:unpert-bounds, bpW:w0:basis#lam, bpW:w0:mass
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w7-measure.tex#bpW:w7:constdef@L215-L215 | D_A,N_A,L_A
EDGE: bpW:w7:unpert-bounds | blueprint-W/parts/w7-measure.tex#bpW:w7:constdef@L216-L216 | beta_* and a_kappa
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w7-measure.tex#bpW:w7:constdef@L215-L217 | lambda_1 and lambda_2
EDGE: bpW:w0:mass | blueprint-W/parts/w7-measure.tex#bpW:w7:constdef@L214-L214 | m > 0 fixed
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: new+sol-review-W-w7a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Only definitions (C1)-(C2), not the later minima, smallness thresholds or positivity conclusions. This split permits Xdef to consume its actual constants without a cycle.

NODE: bpN:p6:ext-numerics
KIND: external
TITLE: Numerics
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#bpN:p6:ext-numerics@L22-L22
PROOF_SOURCE: -
CONTRACT_ID: bpN:p6:ext-numerics
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: 2/e<1; e^{-3 ln2}=1/8; e^2<8, hence ln2>2/3 and 12 ln2>8; sum_{i>=1} 4^{1-i}=4/3; (1-2^{-7})^{-1}=128/127; (1-1/8)^{-1}=8/7 (and e>2, used in bg-sum)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p6
REVIEWER: sol-review-N-d
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external (E1) of Part 6; no hypotheses

NODE: bpN:p6:ext-chain
KIND: external
TITLE: Chain rule for holomorphic maps
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#bpN:p6:ext-chain@L23-L23
PROOF_SOURCE: -
CONTRACT_ID: bpN:p6:ext-chain
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: holomorphic maps F, G composable
SOURCE_QUANTIFIERS: F, G
SOURCE_CONCLUSION: F∘G is holomorphic and D(F∘G)=DF∘G · DG
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p6
REVIEWER: sol-review-N-d
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external (E2) of Part 6

NODE: bpN:p6:setting
KIND: definition
TITLE: Resonant setting
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#bpN:p6:setting@L29-L40
PROOF_SOURCE: -
CONTRACT_ID: bpN:p6:setting
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: D subset C^n; r>0; K>=0; alpha>0; L>=0; Lambda subset Z^n; h holomorphic on V_rD (bpN:p4:domains), regarded as a theta-independent function on D_{r,s} for every s>0; omega=∂_I h : V_rD -> C^n; for the norm |g|_*: g=sum_{j in J} g_j, J finite, g_j in O(r_j,s_j) with finite norm, r_j>=r, s_j>=s, 0<rho<r, 0<sigma<s
SOURCE_QUANTIFIERS: D; r; K; alpha; L; Lambda; h; then (for |g|_*) s, J, g_j, r_j, s_j, rho, sigma
SOURCE_CONCLUSION: defines: (N1) |k·omega(I)|>=alpha for all I in D, k in Z_K\Lambda; (N2) |omega(I)-omega(I0)|_inf<=L|I-I0|_inf whenever I0 in D, I in V_rD, |I-I0|_inf<r; and |g|_*=sum_j (1/2)(rho/(r_j-r+rho)+sigma/(s_j-s+sigma))|g_j|_{r_j,s_j} (depends on the decomposition; equals |g|_{r,s} for J={1}). Item labels cond-nr, cond-L map to this node
CONSTANT_SCOPE: L, alpha, K are data of the setting (no dependence restriction); |g|_* depends on the chosen decomposition and on (rho,sigma)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p4:domains, bpN:p4:norm, bpN:p6#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p4:domains | blueprint-N/parts/p6-normal-form.tex#bpN:p6:setting@L30-L30 | V_rD and D_{r,s} of Definition p4:domains
EDGE: bpN:p4:norm | blueprint-N/parts/p6-normal-form.tex#bpN:p6:setting@L30-L36 | the classes O(r_j,s_j), finite weighted norms ¦g_j¦_{r_j,s_j}, used in the definition of ¦g¦_*
EDGE: bpN:p6#data | blueprint-N/parts/p6-normal-form.tex#bpN:p6:setting@L32-L32 | Z_K and omega=∂_I h in (N1)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p6
REVIEWER: sol-review-N-d
LEAN_STATUS: PROVED
LEAN_REF: IsNonresonant, FreqLipschitz, DivisorBound, IsDecomp, starNorm (KAM/Nekhoroshev/NormalForm/Setting.lean)
LEAN_NOTE: audit N6-1 PASS
NOTE: -

NODE: bpN:p6:lipschitz
KIND: lemma
TITLE: Lipschitz bound from the Hessian
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#bpN:p6:lipschitz@L42-L45
PROOF_SOURCE: blueprint-N/parts/p6-normal-form.tex#bpN:p6:lipschitz@L46-L48
CONTRACT_ID: bpN:p6:lipschitz
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: omega=∂_I h holomorphic on V_rD; operator norm of Domega=∂_I^2 h (max norm on both sides) <= L on V_rD
SOURCE_QUANTIFIERS: D, r, h, L
SOURCE_CONCLUSION: (N2) holds with this L; in particular L=nM_C if every entry of the Hessian has modulus <= M_C
CONSTANT_SCOPE: L is the operator-norm bound on V_rD; M_C a bound on Hessian entries
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p6:lip-seg, bpN:p6:setting, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p6:lip-seg | blueprint-N/parts/p6-normal-form.tex#bpN:p6:lipschitz@L47-L47 | proof step
EDGE: bpN:p6:setting | blueprint-N/parts/p6-normal-form.tex#bpN:p6:lipschitz@L43-L43 | conclusion is condition (N2) of the setting
EDGE: bpN:p4:domains | blueprint-N/parts/p6-normal-form.tex#bpN:p6:lipschitz@L43-L43 | V_rD is the domain of the Hessian and frequency bound
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p6+sol-delta-N-d
REVIEWER: sol-delta2-N-d
LEAN_STATUS: PROVED
LEAN_REF: lipschitz, lipschitz_entries (KAM/Nekhoroshev/NormalForm/Setting.lean)
LEAN_NOTE: audit N6-1 PASS
NOTE: -

NODE: stepN:p6:lip-seg
KIND: step
TITLE: Segment
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:lip-seg@L47-L47
PROOF_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:lip-seg@L47-L47
CONTRACT_ID: stepN:p6:lip-seg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: omega holomorphic on V_rD with operator norm of Domega <= L; I0 in D, I in V_rD, |I-I0|_inf<r
SOURCE_QUANTIFIERS: I0; I
SOURCE_CONCLUSION: segment [I0,I] lies in the convex polydisc P(I0,r) in V_rD and the mean value inequality gives |omega(I)-omega(I0)|_inf<=L|I-I0|_inf
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p4:domains, K:bp:p1:ext-mvt
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p4:domains | blueprint-N/parts/p6-normal-form.tex#stepN:p6:lip-seg@L47-L47 | convexity of the polydisc P(I0,r) contained in V_rD
EDGE: K:bp:p1:ext-mvt | blueprint-N/parts/p6-normal-form.tex#stepN:p6:lip-seg@L47-L47 | mean value inequality along the segment
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p6
REVIEWER: sol-review-N-d
LEAN_STATUS: PROVED
LEAN_REF: lipschitz (KAM/Nekhoroshev/NormalForm/Setting.lean)
LEAN_NOTE: audit N6-1 PASS, row lipschitz (Setting.lean:93): 'segment mean-value proof matches blueprint L43-47' at N6-1-audit-1.md:49.
NOTE: -

NODE: bpN:p6:divisor
KIND: lemma
TITLE: Divisor bound
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#bpN:p6:divisor@L50-L53
PROOF_SOURCE: blueprint-N/parts/p6-normal-form.tex#bpN:p6:divisor@L54-L56
CONTRACT_ID: bpN:p6:divisor
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (N1), (N2) of the setting; K L r<=alpha/p; p>1, q=p/(p-1)
SOURCE_QUANTIFIERS: (D,r,K,alpha,L,Lambda,h); p; then I in V_rD, k in Z_K\Lambda
SOURCE_CONCLUSION: |k·omega(I)|>=alpha-KLr>=alpha/q for all I in V_rD and k in Z_K\Lambda
CONSTANT_SCOPE: none beyond the setting data
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p6:div, bpN:p6:setting, bpN:p6#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p6:div | blueprint-N/parts/p6-normal-form.tex#bpN:p6:divisor@L55-L55 | proof step
EDGE: bpN:p6:setting | blueprint-N/parts/p6-normal-form.tex#bpN:p6:divisor@L51-L51 | hypotheses (N1), (N2)
EDGE: bpN:p6#data | blueprint-N/parts/p6-normal-form.tex#bpN:p6:divisor@L51-L51 | Z_K, p, q
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p6
REVIEWER: sol-review-N-d
LEAN_STATUS: PROVED
LEAN_REF: divisor (KAM/Nekhoroshev/NormalForm/Setting.lean)
LEAN_NOTE: audit N6-1 PASS
NOTE: -

NODE: stepN:p6:div
KIND: step
TITLE: Move to $D$
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:div@L55-L55
PROOF_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:div@L55-L55
CONTRACT_ID: stepN:p6:div
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (N1), (N2); K L r<=alpha/p; I in V_rD
SOURCE_QUANTIFIERS: I; I0 in D with |I-I0|_inf<r; k in Z_K\Lambda
SOURCE_CONCLUSION: |k·omega(I)|>=|k·omega(I0)|-|k|_1|omega(I)-omega(I0)|_inf>=alpha-KLr>=alpha/q
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p6:setting, bpN:p4:domains, bpN:p6#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p6:setting | blueprint-N/parts/p6-normal-form.tex#stepN:p6:div@L55-L55 | (N1) at I0 and (N2) for omega(I)-omega(I0)
EDGE: bpN:p4:domains | blueprint-N/parts/p6-normal-form.tex#stepN:p6:div@L55-L55 | every I in V_rD has some I0 in D with ¦I-I0¦_inf<r (definition of V_rD)
EDGE: bpN:p6#data | blueprint-N/parts/p6-normal-form.tex#stepN:p6:div@L55-L55 | Z_K, q=p/(p-1)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p6
REVIEWER: sol-review-N-d
LEAN_STATUS: PROVED
LEAN_REF: divisor (KAM/Nekhoroshev/NormalForm/Setting.lean)
LEAN_NOTE: audit N6-1 PASS, row divisor (Setting.lean:148: both alpha-KLr and alpha/q bounds on V_rD) at N6-1-audit-1.md:51; helper norm_dotC_le (N6-1-audit-1.md:47).
NOTE: -

NODE: bpN:p6:homological
KIND: proposition
TITLE: Homological equation
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#bpN:p6:homological@L60-L70
PROOF_SOURCE: blueprint-N/parts/p6-normal-form.tex#bpN:p6:homological@L71-L79
CONTRACT_ID: bpN:p6:homological
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (N1), (N2), KLr<=alpha/p; s>0; f in O(r,s) with delta=|f|_{r,s}<infinity; xi=P_Lambda T_K f; phi=sum_{k in Z_K\Lambda} fhat_k(I)/(2πi k·omega(I)) chi_k(theta), chi_k=e^{2πik·theta}
SOURCE_QUANTIFIERS: (D,r,K,alpha,L,Lambda,h); p; s; f
SOURCE_CONCLUSION: xi, phi in O(r,s) are finite sums of characters (trig. polynomials of degree<=K in theta) and (a) {phi,h}+xi=T_K f on D_{r,s} with {phi,h}=∂_theta phi·omega, P_Lambda phi=0, P_Lambda xi=xi, xi=P_{Lambda∩Z_K} f; (b) |xi|_{r,s}<=delta, |T_K f|_{r,s}<=delta, |phi|_{r,s}<=q delta/abar=q delta/(2πalpha); (c) if Lambda=-Lambda, f real on real points and omega(I) real for real I in V_rD then xi, phi real on real points
CONSTANT_SCOPE: constants q=p/(p-1), abar=2πalpha; no dependence on f beyond delta
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p6:hom-def, stepN:p6:hom-norm, stepN:p6:hom-eq, stepN:p6:hom-real, bpN:p6:setting, bpN:p6#data, bpN:p4:norm, bpN:p4:projections, bpN:p5:setting, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p6:hom-def | blueprint-N/parts/p6-normal-form.tex#bpN:p6:homological@L72-L72 | proof step
EDGE: stepN:p6:hom-norm | blueprint-N/parts/p6-normal-form.tex#bpN:p6:homological@L74-L74 | proof step
EDGE: stepN:p6:hom-eq | blueprint-N/parts/p6-normal-form.tex#bpN:p6:homological@L76-L76 | proof step
EDGE: stepN:p6:hom-real | blueprint-N/parts/p6-normal-form.tex#bpN:p6:homological@L78-L78 | proof step
EDGE: bpN:p6:setting | blueprint-N/parts/p6-normal-form.tex#bpN:p6:homological@L61-L61 | hypotheses (N1), (N2)
EDGE: bpN:p6#data | blueprint-N/parts/p6-normal-form.tex#bpN:p6:homological@L61-L62 | Z_K, q, abar, K
EDGE: bpN:p4:norm | blueprint-N/parts/p6-normal-form.tex#bpN:p6:homological@L61-L61 | class O(r,s), norm ¦f¦_{r,s}, Fourier coefficients fhat_k
EDGE: bpN:p4:projections | blueprint-N/parts/p6-normal-form.tex#bpN:p6:homological@L62-L62 | xi=P_Lambda T_K f uses the projections P_S and T_K
EDGE: bpN:p5:setting | blueprint-N/parts/p6-normal-form.tex#bpN:p6:homological@L65-L65 | bracket {phi,h}=∂_theta phi·omega
EDGE: bpN:p4:domains | blueprint-N/parts/p6-normal-form.tex#bpN:p6:homological@L61-L61 | domain D_{r,s}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p6
REVIEWER: sol-review-N-d
LEAN_STATUS: PROVED
LEAN_REF: homGen, homRes, homological (KAM/Nekhoroshev/NormalForm/Homological.lean)
LEAN_NOTE: audit N6-2 PASS (Homological.lean)
NOTE: -

NODE: stepN:p6:hom-def
KIND: step
TITLE: Well defined and holomorphic
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:hom-def@L72-L72
PROOF_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:hom-def@L72-L72
CONTRACT_ID: stepN:p6:hom-def
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: statement of homological; Lemma divisor gives |k·omega|>=alpha/q on V_rD
SOURCE_QUANTIFIERS: k in Z_K\Lambda
SOURCE_CONCLUSION: phihat_k=fhat_k/(2πi k·omega) is holomorphic on V_rD; Z_K∩Lambda and Z_K\Lambda finite; phi, xi are finite sums a_k(I)chi_k(theta) with finite norm so lie in O(r,s); xi=P_Lambda T_K f=P_{Lambda∩Z_K} f
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p6:divisor, bpN:p4:coefficients, bpN:p4:projections, bpN:p4:norm, bpN:p6#data, bpN:p6:setting, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p6:divisor | blueprint-N/parts/p6-normal-form.tex#stepN:p6:hom-def@L72-L72 | nonvanishing of k·omega with modulus >= alpha/q
EDGE: bpN:p4:coefficients | blueprint-N/parts/p6-normal-form.tex#stepN:p6:hom-def@L72-L72 | (a) holomorphy of coefficients, (c) finite sums with finite weighted sup lie in O(r,s)
EDGE: bpN:p4:projections | blueprint-N/parts/p6-normal-form.tex#stepN:p6:hom-def@L72-L72 | xi=P_Lambda T_K f=P_{Lambda∩Z_K} f
EDGE: bpN:p4:norm | blueprint-N/parts/p6-normal-form.tex#stepN:p6:hom-def@L72-L72 | membership in O(r,s) and finiteness of the weighted sup
EDGE: bpN:p6#data | blueprint-N/parts/p6-normal-form.tex#stepN:p6:hom-def@L72-L72 | Z_K
EDGE: bpN:p6:setting | blueprint-N/parts/p6-normal-form.tex#stepN:p6:hom-def@L72-L72 | the frequency omega or the decomposition of g is used directly
EDGE: bpN:p4:domains | blueprint-N/parts/p6-normal-form.tex#stepN:p6:hom-def@L72-L72 | V_rD or D_{r,s} (including shrunken widths) is used directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p6+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: homological (KAM/Nekhoroshev/NormalForm/Homological.lean)
LEAN_NOTE: audit N6-2 PASS, rows homGenParam, genCoeff, genCoeff_differentiableOn, divisor_ne_zero (Homological) at N6-2-audit-1.md:146 to N6-2-audit-1.md:173; homological (Homological:491) at N6-2-audit-1.md:64.
NOTE: -

NODE: stepN:p6:hom-norm
KIND: step
TITLE: Norms
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:hom-norm@L74-L74
PROOF_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:hom-norm@L74-L74
CONTRACT_ID: stepN:p6:hom-norm
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: statement of homological; phi, xi as constructed in hom-def
SOURCE_QUANTIFIERS: I in V_rD; k in Z_K\Lambda
SOURCE_CONCLUSION: |phihat_k(I)|<=q/(2πalpha)|fhat_k(I)|; summing with weights e^{2π|k|_1 s} and sup over I gives |phi|_{r,s}<=q delta/abar; |xi|_{r,s}, |T_K f|_{r,s}<=delta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p6:divisor, bpN:p4:projections, stepN:p6:hom-def, bpN:p4:norm, bpN:p6#data, bpN:p6:setting, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p6:divisor | blueprint-N/parts/p6-normal-form.tex#stepN:p6:hom-norm@L74-L74 | divisor bound ¦k·omega¦>=alpha/q
EDGE: bpN:p4:projections | blueprint-N/parts/p6-normal-form.tex#stepN:p6:hom-norm@L74-L74 | norm bounds for xi and T_K f
EDGE: stepN:p6:hom-def | blueprint-N/parts/p6-normal-form.tex#stepN:p6:hom-norm@L74-L74 | phi is the finite sum of hom-def with coefficients phihat_k
EDGE: bpN:p4:norm | blueprint-N/parts/p6-normal-form.tex#stepN:p6:hom-norm@L74-L74 | weighted norm sum_k ¦.¦e^{2π¦k¦_1 s}
EDGE: bpN:p6#data | blueprint-N/parts/p6-normal-form.tex#stepN:p6:hom-norm@L74-L74 | q, abar
EDGE: bpN:p6:setting | blueprint-N/parts/p6-normal-form.tex#stepN:p6:hom-norm@L74-L74 | the frequency omega or the decomposition of g is used directly
EDGE: bpN:p4:domains | blueprint-N/parts/p6-normal-form.tex#stepN:p6:hom-norm@L74-L74 | I ranges over V_rD and the weighted bound is obtained by its supremum on that action domain
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p6+sol-delta-N-d
REVIEWER: sol-delta2-N-d
LEAN_STATUS: PROVED
LEAN_REF: homological (KAM/Nekhoroshev/NormalForm/Homological.lean)
LEAN_NOTE: audit N6-2 PASS, row norm_genCoeff_le (Homological:172, correct modulus 2 pi|k.omega|) at N6-2-audit-1.md:174 with homResParam_eq_projMode and W4 projections for T_K f and xi; carrier homological.
NOTE: -

NODE: stepN:p6:hom-eq
KIND: step
TITLE: The equation
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:hom-eq@L76-L76
PROOF_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:hom-eq@L76-L76
CONTRACT_ID: stepN:p6:hom-eq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: statement of homological; phi, xi as in hom-def; h independent of theta
SOURCE_QUANTIFIERS: k in Z^n
SOURCE_CONCLUSION: {phi,h}=sum_j ∂_{theta_j}phi omega_j has coefficients 2πi(k·omega)phihat_k=fhat_k for k in Z_K\Lambda and 0 otherwise; adding xihat_k gives the coefficients of T_K f; coefficients determine the function, hence {phi,h}+xi=T_K f
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p4:coefficients, bpN:p5:setting, stepN:p6:hom-def, bpN:p6#data, bpN:p4:norm, bpN:p6:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p4:coefficients | blueprint-N/parts/p6-normal-form.tex#stepN:p6:hom-eq@L76-L76 | (b) coefficients of ∂_theta phi, (d) coefficients determine the function
EDGE: bpN:p5:setting | blueprint-N/parts/p6-normal-form.tex#stepN:p6:hom-eq@L76-L76 | bracket {phi,h} for theta-independent h
EDGE: stepN:p6:hom-def | blueprint-N/parts/p6-normal-form.tex#stepN:p6:hom-eq@L76-L76 | phi, xi finite sums in O(r,s) with the stated coefficients
EDGE: bpN:p6#data | blueprint-N/parts/p6-normal-form.tex#stepN:p6:hom-eq@L76-L76 | Z_K
EDGE: bpN:p4:norm | blueprint-N/parts/p6-normal-form.tex#stepN:p6:hom-eq@L76-L76 | O(r,s), Fourier coefficients or weighted norms are used directly
EDGE: bpN:p6:setting | blueprint-N/parts/p6-normal-form.tex#stepN:p6:hom-eq@L76-L76 | the frequency omega or the decomposition of g is used directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p6+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: homological (KAM/Nekhoroshev/NormalForm/Homological.lean)
LEAN_NOTE: audit N6-2 PASS, rows hasFDerivAt_genTerm, fderiv_homGenParam, dotC_eq_sum, directional_homGenParam (Homological:234-278) at N6-2-audit-1.md:180; proof paragraph 'directional identity plus the resonant finite sum partitions the cutoff, proving the equation pointwise'.
NOTE: -

NODE: stepN:p6:hom-real
KIND: step
TITLE: Reality
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:hom-real@L78-L78
PROOF_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:hom-real@L78-L78
CONTRACT_ID: stepN:p6:hom-real
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Lambda=-Lambda; f real on real points; omega(I) real for real I in V_rD
SOURCE_QUANTIFIERS: real I; k with k, -k not in Lambda
SOURCE_CONCLUSION: conj(fhat_k)=fhat_{-k}; conj(phihat_k)=phihat_{-k}; Z_K\Lambda symmetric; a finite sum with conj(a_k)=a_{-k} is real at real theta; same for xi
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p4:norm, stepN:p6:hom-def, bpN:p6#data, bpN:p6:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p4:norm | blueprint-N/parts/p6-normal-form.tex#stepN:p6:hom-real@L78-L78 | Fourier coefficient as an integral in theta (conjugate the integral)
EDGE: stepN:p6:hom-def | blueprint-N/parts/p6-normal-form.tex#stepN:p6:hom-real@L78-L78 | phihat_k=fhat_k/(2πi k·omega) and xi=P_{Lambda∩Z_K} f are finite sums
EDGE: bpN:p6#data | blueprint-N/parts/p6-normal-form.tex#stepN:p6:hom-real@L78-L78 | Z_K symmetric
EDGE: bpN:p6:setting | blueprint-N/parts/p6-normal-form.tex#stepN:p6:hom-real@L78-L78 | the frequency omega or the decomposition of g is used directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p6+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: homological (KAM/Nekhoroshev/NormalForm/Homological.lean)
LEAN_NOTE: audit N6-2 PASS, rows im_tsum_indicator_eq_zero (:304), conj_dotC, dotC_neg, conj_coeff (:330) at N6-2-audit-1.md:186; conditional reality conclusion (Lambda=-Lambda, f real, real frequency) at N6-2-audit-1.md:120.
NOTE: -

NODE: bpN:p6:bracket-g
KIND: lemma
TITLE: Bracket with a decomposed $g$
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#bpN:p6:bracket-g@L81-L85
PROOF_SOURCE: blueprint-N/parts/p6-normal-form.tex#bpN:p6:bracket-g@L86-L89
CONTRACT_ID: bpN:p6:bracket-g
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: phi in O(r,s); g=sum_{j in J} g_j as in the setting (g_j in O(r_j,s_j), r_j>=r, s_j>=s, finite norms); 0<rho<r, 0<sigma<s
SOURCE_QUANTIFIERS: phi; g, J, g_j; rho, sigma
SOURCE_CONCLUSION: {g,phi} in O(r-rho,s-sigma) and |{g,phi}|_{r-rho,s-sigma}<=(2/(e rho sigma))|g|_*|phi|_{r,s}<=(2/(rho sigma))|g|_*|phi|_{r,s}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p6:bg-term, stepN:p6:bg-sum, bpN:p6:setting, bpN:p4:norm, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p6:bg-term | blueprint-N/parts/p6-normal-form.tex#bpN:p6:bracket-g@L87-L87 | proof step
EDGE: stepN:p6:bg-sum | blueprint-N/parts/p6-normal-form.tex#bpN:p6:bracket-g@L88-L88 | proof step
EDGE: bpN:p6:setting | blueprint-N/parts/p6-normal-form.tex#bpN:p6:bracket-g@L82-L82 | decomposition of g and the norm ¦g¦_*
EDGE: bpN:p4:norm | blueprint-N/parts/p6-normal-form.tex#bpN:p6:bracket-g@L82-L83 | classes O(r,s), norms
EDGE: bpN:p5:setting | blueprint-N/parts/p6-normal-form.tex#bpN:p6:bracket-g@L82-L82 | bracket {g,phi}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p6
REVIEWER: sol-review-N-d
LEAN_STATUS: PROVED
LEAN_REF: bracket_g (KAM/Nekhoroshev/NormalForm/BracketDecomp.lean)
LEAN_NOTE: audit N6-3 PASS WITH NOTES
NOTE: -

NODE: stepN:p6:bg-term
KIND: step
TITLE: One term
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:bg-term@L87-L87
PROOF_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:bg-term@L87-L87
CONTRACT_ID: stepN:p6:bg-term
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: phi, g_j as in bracket-g; admissible: r-rho<r_j, s-sigma<s_j
SOURCE_QUANTIFIERS: one term g_j
SOURCE_CONCLUSION: |{g_j,phi}|_{r-rho,s-sigma}<=(2/(e rho sigma))·(1/2)(rho/(r_j-r+rho)+sigma/(s_j-s+sigma))|g_j|_{r_j,s_j}|phi|_{r,s}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p4:bracket, bpN:p6:setting, bpN:p4:norm, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p4:bracket | blueprint-N/parts/p6-normal-form.tex#stepN:p6:bg-term@L87-L87 | bracket estimate with (u,v;r0,s0)->(g_j,phi;r_j,s_j)
EDGE: bpN:p6:setting | blueprint-N/parts/p6-normal-form.tex#stepN:p6:bg-term@L87-L87 | weight (1/2)(rho/(r_j-r+rho)+sigma/(s_j-s+sigma)) of the term in ¦g¦_*
EDGE: bpN:p4:norm | blueprint-N/parts/p6-normal-form.tex#stepN:p6:bg-term@L87-L87 | norms ¦g_j¦_{r_j,s_j}, ¦phi¦_{r,s}
EDGE: bpN:p5:setting | blueprint-N/parts/p6-normal-form.tex#stepN:p6:bg-term@L87-L87 | the Poisson bracket and its bilinearity/sign are used directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p6+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: bracket_g (KAM/Nekhoroshev/NormalForm/BracketDecomp.lean)
LEAN_NOTE: audit N6-3 PASS WITH NOTES, row bracket_g (BracketDecomp.lean:92) exact constants 2/(e rho sigma), 2/(rho sigma) at N6-3-audit-1.md:40; proof paragraph 'For each summand the proof applies wbound_bracket' at N6-3-audit-1.md:86.
NOTE: -

NODE: stepN:p6:bg-sum
KIND: step
TITLE: Sum
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:bg-sum@L88-L88
PROOF_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:bg-sum@L88-L88
CONTRACT_ID: stepN:p6:bg-sum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: terms of bg-term; bilinearity of the bracket; triangle inequality
SOURCE_QUANTIFIERS: sum over j in J
SOURCE_CONCLUSION: |{g,phi}|<=(2/(e rho sigma))|g|_*|phi|; and 2/e<=2 numerically (e>2)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p6:ext-numerics, bpN:p6:setting, stepN:p6:bg-term, bpN:p4:norm, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p6:ext-numerics | blueprint-N/parts/p6-normal-form.tex#stepN:p6:bg-sum@L88-L88 | e>2 for the last inequality
EDGE: bpN:p6:setting | blueprint-N/parts/p6-normal-form.tex#stepN:p6:bg-sum@L88-L88 | sum over j of the weighted terms is ¦g¦_*
EDGE: stepN:p6:bg-term | blueprint-N/parts/p6-normal-form.tex#stepN:p6:bg-sum@L88-L88 | estimate of each term
EDGE: bpN:p4:norm | blueprint-N/parts/p6-normal-form.tex#stepN:p6:bg-sum@L88-L88 | O(r,s), Fourier coefficients or weighted norms are used directly
EDGE: bpN:p5:setting | blueprint-N/parts/p6-normal-form.tex#stepN:p6:bg-sum@L88-L88 | the Poisson bracket and its bilinearity/sign are used directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p6+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: bracket_g (KAM/Nekhoroshev/NormalForm/BracketDecomp.lean)
LEAN_NOTE: audit N6-3 PASS WITH NOTES, rows stepN:p6:bg-sum wsum_finset_sum_le (:48) and poissonBracket_sum (:77) at N6-3-audit-1.md:43.
NOTE: -

NODE: bpN:p6:iterative
KIND: theorem
TITLE: Iterative Lemma
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#bpN:p6:iterative@L93-L108
PROOF_SOURCE: blueprint-N/parts/p6-normal-form.tex#bpN:p6:iterative@L109-L127
CONTRACT_ID: bpN:p6:iterative
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (N1), (N2), KLr<=alpha/p (p>1, q=p/(p-1)); s>0; rho,sigma>0 with 2rho<r, 2sigma<s; abar=2πalpha; H=h+g+f on D_{r,s}, g=sum_{j in J} g_j as in the setting (any finite decomposition), f in O(r,s); delta=|f|_{r,s}<=abar rho sigma/(4q) (equivalently u=q delta/(abar rho sigma)<=1/4)
SOURCE_QUANTIFIERS: (D,r,K,alpha,L,Lambda,h); p; s; rho; sigma; g, J, g_j; f
SOURCE_CONCLUSION: there is phi in O(r,s) (that of the homological equation, |phi|_{r,s}<=q delta/abar) such that Phi=X^1_phi satisfies (a) Phi holomorphic on D_{r-3rho/2,s-3sigma/2} into D_{r-rho,s-sigma}, canonical (DPhi^T J DPhi=J), Phi(theta+k,I)=Phi(theta,I)+(k,0), injective on D_{r-2rho,s-2sigma} with left inverse X^{-1}_phi; (b) nu_{rho,sigma}(Phi-id)<=u, |Phi_theta-theta|_inf<=q delta/(abar rho), |Phi_I-I|_inf<=q delta/(e abar sigma), |DPhi-1|_nu<=2u on D_{r-2rho,s-2sigma}; (c) H∘Phi=h+g_++f_+ on D_{r-2rho,s-2sigma}, g_+=g+P_Lambda T_K f, |g_+-g|_{r,s}<=delta, f_+ in O(r-2rho,s-2sigma); (d) |f_+|_{r-2rho,s-2sigma}<=(1-2q delta/(abar rho sigma))^{-1}(2q/(e abar rho sigma)(|g|_*+delta)+e^{-2πK sigma})delta; (e) if Lambda=-Lambda and h,g,f real on real points then phi, g_+, f_+ real on real points and Phi maps real points to real points
CONSTANT_SCOPE: all constants explicit; depend only on (n,r,s,rho,sigma,K,alpha,L,p) and on delta, |g|_*; no dependence on f or H beyond delta and |g|_*
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p6:it-gen, stepN:p6:it-map, stepN:p6:it-taylor, stepN:p6:it-decomp, stepN:p6:it-integrand, stepN:p6:it-terms, stepN:p6:it-real, bpN:p6:setting, bpN:p6#data, bpN:p6:homological, bpN:p4:norm, bpN:p4:domains, bpN:p5:setting, bpN:p5:flow, bpN:p5:canonical-map, bpN:p4:projections
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p6:it-gen | blueprint-N/parts/p6-normal-form.tex#bpN:p6:iterative@L110-L110 | proof step
EDGE: stepN:p6:it-map | blueprint-N/parts/p6-normal-form.tex#bpN:p6:iterative@L112-L112 | proof step
EDGE: stepN:p6:it-taylor | blueprint-N/parts/p6-normal-form.tex#bpN:p6:iterative@L114-L114 | proof step
EDGE: stepN:p6:it-decomp | blueprint-N/parts/p6-normal-form.tex#bpN:p6:iterative@L117-L117 | proof step
EDGE: stepN:p6:it-integrand | blueprint-N/parts/p6-normal-form.tex#bpN:p6:iterative@L121-L121 | proof step
EDGE: stepN:p6:it-terms | blueprint-N/parts/p6-normal-form.tex#bpN:p6:iterative@L124-L124 | proof step
EDGE: stepN:p6:it-real | blueprint-N/parts/p6-normal-form.tex#bpN:p6:iterative@L126-L126 | proof step
EDGE: bpN:p6:setting | blueprint-N/parts/p6-normal-form.tex#bpN:p6:iterative@L94-L94 | hypotheses (N1), (N2), decomposition of g and ¦g¦_*
EDGE: bpN:p6#data | blueprint-N/parts/p6-normal-form.tex#bpN:p6:iterative@L94-L95 | q, abar, K, Z_K
EDGE: bpN:p6:homological | blueprint-N/parts/p6-normal-form.tex#bpN:p6:iterative@L96-L96 | phi is the generating function of the homological equation
EDGE: bpN:p4:norm | blueprint-N/parts/p6-normal-form.tex#bpN:p6:iterative@L94-L94 | classes O(r,s), norms
EDGE: bpN:p4:domains | blueprint-N/parts/p6-normal-form.tex#bpN:p6:iterative@L98-L98 | domains D_{r-c rho,s-c sigma}
EDGE: bpN:p5:setting | blueprint-N/parts/p6-normal-form.tex#bpN:p6:iterative@L99-L99 | nu=nu_{rho,sigma}, bracket, J
EDGE: bpN:p5:flow | blueprint-N/parts/p6-normal-form.tex#bpN:p6:iterative@L96-L96 | time-one map Phi=X^1_phi
EDGE: bpN:p5:canonical-map | blueprint-N/parts/p6-normal-form.tex#bpN:p6:iterative@L98-L98 | items (d),(e),(b) of the canonical-map proposition give (a)
EDGE: bpN:p4:projections | blueprint-N/parts/p6-normal-form.tex#bpN:p6:iterative@L101-L101 | g_+=g+P_Lambda T_K f
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p6
REVIEWER: sol-review-N-d
LEAN_STATUS: PROVED
LEAN_REF: iterMap, iterG, iterF, IterHyp, iterU, iterative_direct_a, iterative_direct_b, iterHyp_of_source (KAM/Nekhoroshev/NormalForm/IterativeMap.lean); iterative_direct_c, iterative_direct_d (KAM/Nekhoroshev/NormalForm/IterativeRemainder.lean); iterative_direct_e (KAM/Nekhoroshev/NormalForm/IterativeReal.lean)
LEAN_NOTE: composite of audits N6-5 PASS WITH NOTES (a),(b), source wrapper iterHyp_of_source + N6-6 PASS WITH NOTES (c),(d) + N6-7 PASS WITH NOTES (e); source form via iterHyp_of_source
NOTE: -

NODE: stepN:p6:it-gen
KIND: step
TITLE: The generating function
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-gen@L110-L110
PROOF_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-gen@L110-L110
CONTRACT_ID: stepN:p6:it-gen
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: statement of iterative; homological equation
SOURCE_QUANTIFIERS: phi, xi
SOURCE_CONCLUSION: phi, xi exist with {phi,h}+xi=T_K f, |xi|,|T_K f|<=delta, |phi|_{r,s}<=q delta/abar; eps:=|phi|_{r,s}/(rho sigma)<=u<=1/4 and eta:=2|phi|_{r,s}/(rho sigma)<=2u<=1/2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p6:homological, bpN:p4:norm, bpN:p6#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p6:homological | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-gen@L110-L110 | generating function and its norm
EDGE: bpN:p4:norm | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-gen@L110-L110 | norms ¦phi¦_{r,s}
EDGE: bpN:p6#data | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-gen@L110-L110 | q, abar
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p6
REVIEWER: sol-review-N-d
LEAN_STATUS: PROVED
LEAN_REF: homological_direct (KAM/Nekhoroshev/NormalForm/Homological.lean); iterHyp_of_source (KAM/Nekhoroshev/NormalForm/IterativeMap.lean)
LEAN_NOTE: audit N6-5 PASS WITH NOTES, row IterHyp.canon (it-gen / it-map bridge, uses the homological_direct conjuncts) at N6-5-audit-1.md:31, iterU_le (u<=1/4) and phi_div at N6-5-audit-1.md:30; homological_direct audited in N6-2 N6-2-audit-1.md:63.
NOTE: -

NODE: stepN:p6:it-map
KIND: step
TITLE: Items (a), (b)
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-map@L112-L112
PROOF_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-map@L112-L112
CONTRACT_ID: stepN:p6:it-map
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: statement of iterative; eps<=1/2 from it-gen; rho<r/2, sigma<s/2
SOURCE_QUANTIFIERS: Phi=X^1_phi
SOURCE_CONCLUSION: items (a) and (b) of the Iterative Lemma: domains, canonical, periodic, injective, displacement bounds nu(Phi-id)<=u, |Phi_theta-theta|<=q delta/(abar rho), |Phi_I-I|<=q delta/(e abar sigma), |DPhi-1|_nu<=2u
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p5:canonical-map, stepN:p6:it-gen, bpN:p5:setting, bpN:p6#data, bpN:p4:domains, bpN:p4:norm
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p5:canonical-map | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-map@L112-L112 | items (a)-(e) with eps<=1/2
EDGE: stepN:p6:it-gen | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-map@L112-L112 | ¦phi¦<=q delta/abar and eps<=u<=1/4
EDGE: bpN:p5:setting | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-map@L112-L112 | scaled norm nu_{rho,sigma}
EDGE: bpN:p6#data | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-map@L112-L112 | q, abar
EDGE: bpN:p4:domains | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-map@L112-L112 | V_rD or D_{r,s} (including shrunken widths) is used directly
EDGE: bpN:p4:norm | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-map@L112-L112 | O(r,s), Fourier coefficients or weighted norms are used directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p6+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: iterative_direct_a, iterative_direct_b (KAM/Nekhoroshev/NormalForm/IterativeMap.lean)
LEAN_NOTE: audit N6-5 PASS WITH NOTES, rows labelled it-map: iterative_direct_a (:131) and iterative_direct_b (:159) at N6-5-audit-1.md:33 and N6-5-audit-1.md:34.
NOTE: -

NODE: stepN:p6:it-taylor
KIND: step
TITLE: Taylor identity
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-taylor@L114-L115
PROOF_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-taylor@L114-L115
CONTRACT_ID: stepN:p6:it-taylor
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: statement of iterative; homological equation; eta<=1/2
SOURCE_QUANTIFIERS: f0=g+T_K f; w={h,phi}; t in [0,1]
SOURCE_CONCLUSION: f0 in O(r-rho,s-sigma) of finite norm; w=-{phi,h}=xi-T_K f has finite norm; on D_{r-2rho,s-2sigma}: (h+f0)∘Phi=h+w+f0+R with R=int_0^1 {(1-t)w+f0,phi}∘X^t_phi dt, h+w+f0=h+g+xi=h+g_+, (1-t)w+f0=g+f_t with f_t=(1-t)xi+t T_K f
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p6:homological, bpN:p5:setting, bpN:p5:transform, stepN:p6:it-gen, bpN:p4:norm#monotone, bpN:p4:projections, bpN:p4:domains, bpN:p4:norm, bpN:p6:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p6:homological | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-taylor@L114-L114 | (a) {phi,h}+xi=T_K f
EDGE: bpN:p5:setting | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-taylor@L114-L114 | antisymmetry and definition of the bracket
EDGE: bpN:p5:transform | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-taylor@L114-L114 | Taylor/transform identity with data (r-rho,s-sigma;r,s), admissible since eta<=1/2
EDGE: stepN:p6:it-gen | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-taylor@L114-L114 | eta<=1/2
EDGE: bpN:p4:norm#monotone | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-taylor@L114-L114 | ¦g¦_{r,s}<=sum¦g_j¦ and monotonicity give finite norm of f0 on O(r-rho,s-sigma)
EDGE: bpN:p4:projections | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-taylor@L114-L114 | T_K f in O(r,s) with finite norm
EDGE: bpN:p4:domains | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-taylor@L114-L114 | V_rD or D_{r,s} (including shrunken widths) is used directly
EDGE: bpN:p4:norm | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-taylor@L114-L114 | O(r,s), Fourier coefficients or weighted norms are used directly
EDGE: bpN:p6:setting | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-taylor@L114-L114 | the frequency omega or the decomposition of g is used directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p6+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: iterative_direct_c (KAM/Nekhoroshev/NormalForm/IterativeRemainder.lean)
LEAN_NOTE: audit N6-6 PASS WITH NOTES, rows labelled stepN:p6:it-taylor: IterHyp.compose (:140), IterHyp.bracket_eq (:161) at N6-6-audit-1.md:27 and N6-6-audit-1.md:29.
NOTE: -

NODE: stepN:p6:it-decomp
KIND: step
TITLE: Decomposition of $H\circ\Phi$
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-decomp@L117-L119
PROOF_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-decomp@L117-L119
CONTRACT_ID: stepN:p6:it-decomp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: it-taylor identity; f-T_K f in O(r,s)
SOURCE_QUANTIFIERS: f_+
SOURCE_CONCLUSION: H∘Phi=h+g_++f_+ on D_{r-2rho,s-2sigma} with f_+:=R+(f-T_K f)∘Phi, both terms holomorphic and periodic so f_+ in O(r-2rho,s-2sigma) once the norm is finite; this is (c), and |g_+-g|=|xi|<=delta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p6:it-taylor, bpN:p5:composition, bpN:p5:composition-integral, bpN:p4:projections, bpN:p4:domains, bpN:p4:norm
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p6:it-taylor | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-decomp@L117-L117 | identity (h+f0)∘Phi=h+g_++R
EDGE: bpN:p5:composition | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-decomp@L119-L119 | (ii): holomorphy and periodicity of compositions
EDGE: bpN:p5:composition-integral | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-decomp@L119-L119 | holomorphy and periodicity of the integral remainder R
EDGE: bpN:p4:projections | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-decomp@L117-L117 | f-T_K f in O(r,s)
EDGE: bpN:p4:domains | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-decomp@L117-L117 | V_rD or D_{r,s} (including shrunken widths) is used directly
EDGE: bpN:p4:norm | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-decomp@L117-L117 | O(r,s), Fourier coefficients or weighted norms are used directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p6+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: iterative_direct_c (KAM/Nekhoroshev/NormalForm/IterativeRemainder.lean)
LEAN_NOTE: audit N6-6 PASS WITH NOTES, row labelled it-decomp/it-terms: IterHyp.iterF_class_bound (:315) at N6-6-audit-1.md:33 (transform, composition_integral, truncation_tail, composition_series).
NOTE: -

NODE: stepN:p6:it-integrand
KIND: step
TITLE: The integrand
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-integrand@L121-L122
PROOF_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-integrand@L121-L122
CONTRACT_ID: stepN:p6:it-integrand
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: it-taylor; bracket-g; f_t affine in t
SOURCE_QUANTIFIERS: v_t={g+f_t,phi}
SOURCE_CONCLUSION: v_t in O(r-rho,s-sigma) affine in t, (t,z)->v_t(z) and Dv_t continuous; |v_t|_{r-rho,s-sigma}<=(2/(e rho sigma))(|g|_*+delta)|phi|_{r,s}<=(2q/(e abar rho sigma))(|g|_*+delta)delta=:V
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p6:bracket-g, bpN:p4:bracket, stepN:p6:it-taylor, stepN:p6:it-gen, bpN:p6:setting, bpN:p4:norm, bpN:p5:setting, bpN:p6#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p6:bracket-g | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-integrand@L121-L121 | bracket with the decomposed g
EDGE: bpN:p4:bracket | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-integrand@L121-L121 | single-term decomposition f_t with ¦f_t¦<=delta
EDGE: stepN:p6:it-taylor | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-integrand@L121-L121 | f_t=(1-t)xi+t T_K f and the form of the integrand
EDGE: stepN:p6:it-gen | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-integrand@L121-L121 | ¦phi¦_{r,s}<=q delta/abar
EDGE: bpN:p6:setting | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-integrand@L121-L121 | ¦g¦_* with the added term f_t of weight 1
EDGE: bpN:p4:norm | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-integrand@L121-L121 | O(r,s), Fourier coefficients or weighted norms are used directly
EDGE: bpN:p5:setting | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-integrand@L121-L121 | the Poisson bracket and its bilinearity/sign are used directly
EDGE: bpN:p6#data | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-integrand@L121-L121 | Z_K, q or abar is used directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p6+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: iterative_direct_c (KAM/Nekhoroshev/NormalForm/IterativeRemainder.lean)
LEAN_NOTE: audit N6-6 PASS WITH NOTES, rows labelled stepN:p6:it-integrand: IterHyp.remIntegrand (:178), IterHyp.integrand (:185: class, weighted bound, joint continuity of v and Dv) at N6-6-audit-1.md:32.
NOTE: -

NODE: stepN:p6:it-terms
KIND: step
TITLE: The two terms
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-terms@L124-L124
PROOF_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-terms@L124-L124
CONTRACT_ID: stepN:p6:it-terms
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: it-taylor, it-integrand, it-gen; Lemma p4:projections
SOURCE_QUANTIFIERS: R, (f-T_K f)∘Phi
SOURCE_CONCLUSION: |R|_{r-2rho,s-2sigma}<=(1-eta)^{-1}V; |f-T_K f|_{r-rho,s-sigma}<=e^{-2πK sigma}delta and |(f-T_K f)∘Phi|<=(1-eta)^{-1}e^{-2πK sigma}delta; adding and (1-eta)^{-1}<=(1-2q delta/(abar rho sigma))^{-1} gives (d)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p5:composition-integral, stepN:p6:it-taylor, stepN:p6:it-integrand, stepN:p6:it-gen, bpN:p4:projections, bpN:p4:norm#monotone, bpN:p5:composition, bpN:p4:norm, bpN:p4:domains, bpN:p6#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p5:composition-integral | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-terms@L124-L124 | bound for R with the data of it-taylor
EDGE: stepN:p6:it-taylor | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-terms@L124-L124 | data and the integral formula for R
EDGE: stepN:p6:it-integrand | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-terms@L124-L124 | the bound V
EDGE: stepN:p6:it-gen | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-terms@L124-L124 | eta<=2q delta/(abar rho sigma)
EDGE: bpN:p4:projections | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-terms@L124-L124 | ¦f-T_K f¦_{r,s-sigma}<=e^{-2πK sigma}¦f¦_{r,s}
EDGE: bpN:p4:norm#monotone | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-terms@L124-L124 | monotonicity ¦.¦_{r-rho,s-sigma}<=¦.¦_{r,s-sigma}
EDGE: bpN:p5:composition | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-terms@L124-L124 | (ii): norm of a composition (f-T_K f)∘Phi
EDGE: bpN:p4:norm | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-terms@L124-L124 | O(r,s), Fourier coefficients or weighted norms are used directly
EDGE: bpN:p4:domains | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-terms@L124-L124 | V_rD or D_{r,s} (including shrunken widths) is used directly
EDGE: bpN:p6#data | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-terms@L124-L124 | Z_K, q or abar is used directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p6+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: iterative_direct_d (KAM/Nekhoroshev/NormalForm/IterativeRemainder.lean)
LEAN_NOTE: audit N6-6 PASS WITH NOTES, row labelled it-decomp/it-terms IterHyp.iterF_class_bound (:315) at N6-6-audit-1.md:33; (d) iterative_direct_d (:418) states the final remainder bound (N6-6-audit-1.md:35).
NOTE: -

NODE: stepN:p6:it-real
KIND: step
TITLE: Reality
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-real@L126-L126
PROOF_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-real@L126-L126
CONTRACT_ID: stepN:p6:it-real
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Lambda=-Lambda; h,g,f real on real points
SOURCE_QUANTIFIERS: real points
SOURCE_CONCLUSION: omega real at real points; phi, xi real (homological (c)); Phi preserves real points; g_+=g+xi real and f_+=H∘Phi-h-g_+ real on real points of D_{r-2rho,s-2sigma}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p6:homological, bpN:p5:canonical-map, stepN:p6:it-decomp, bpN:p4:domains, bpN:p6:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p6:homological | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-real@L126-L126 | (c) reality of phi, xi
EDGE: bpN:p5:canonical-map | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-real@L126-L126 | (b) Phi preserves real points
EDGE: stepN:p6:it-decomp | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-real@L126-L126 | f_+=H∘Phi-h-g_+ from the decomposition
EDGE: bpN:p4:domains | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-real@L126-L126 | V_rD or D_{r,s} (including shrunken widths) is used directly
EDGE: bpN:p6:setting | blueprint-N/parts/p6-normal-form.tex#stepN:p6:it-real@L126-L126 | the frequency omega or the decomposition of g is used directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p6+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: iterative_direct_e (KAM/Nekhoroshev/NormalForm/IterativeReal.lean)
LEAN_NOTE: audit N6-7 PASS WITH NOTES, rows labelled stepN:p6:it-real: freq_im_real (IterativeReal:33) and iterative_direct_e (IterativeReal:89) at N6-7-audit-1.md:33 and N6-7-audit-1.md:36.
NOTE: -

NODE: bpN:p6:iterative-direct
KIND: corollary
TITLE: Iterative Lemma, direct divisor form
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#bpN:p6:iterative-direct@L129-L134
PROOF_SOURCE: blueprint-N/parts/p6-normal-form.tex#bpN:p6:iterative-direct@L135-L138
CONTRACT_ID: bpN:p6:iterative-direct
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: D subset C^n; r>0; K>=0; alpha>0; Lambda subset Z^n; p>1, q=p/(p-1); h holomorphic on V_rD with omega=∂_I h; hypothesis (N-dir): |k·omega(I)|>=alpha/q for all I in V_rD, k in Z_K\Lambda (in place of (N1), (N2), KLr<=alpha/p); the other hypotheses of the homological equation and the Iterative Lemma on s, rho, sigma, g, f, delta
SOURCE_QUANTIFIERS: D; r; K; alpha; Lambda; p; h; then s, rho, sigma, g, f
SOURCE_CONCLUSION: Proposition homological, Theorem iterative (all of (a)-(e), with the same constants and hypotheses on s,rho,sigma,g,f,delta), and Remark iterative-special hold verbatim under (N-dir). The special-case remark is excluded from this graph by the ownership/root-closure ruling, but is part of the source conclusion.
CONSTANT_SCOPE: as in the Iterative Lemma; L does not occur
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p6:dir-use, stepN:p6:dir-concl, bpN:p6:homological, bpN:p6:iterative, bpN:p6:setting, bpN:p6#data, bpN:p4:domains, bpN:p4:norm, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p6:dir-use | blueprint-N/parts/p6-normal-form.tex#bpN:p6:iterative-direct@L136-L136 | proof step
EDGE: stepN:p6:dir-concl | blueprint-N/parts/p6-normal-form.tex#bpN:p6:iterative-direct@L137-L137 | proof step
EDGE: bpN:p6:homological | blueprint-N/parts/p6-normal-form.tex#bpN:p6:iterative-direct@L132-L132 | conclusion: the homological equation under (N-dir)
EDGE: bpN:p6:iterative | blueprint-N/parts/p6-normal-form.tex#bpN:p6:iterative-direct@L132-L132 | conclusion: the Iterative Lemma under (N-dir)
EDGE: bpN:p6:setting | blueprint-N/parts/p6-normal-form.tex#bpN:p6:iterative-direct@L132-L132 | g as in the setting, ¦g¦_*
EDGE: bpN:p6#data | blueprint-N/parts/p6-normal-form.tex#bpN:p6:iterative-direct@L130-L131 | Z_K, p, q
EDGE: bpN:p4:domains | blueprint-N/parts/p6-normal-form.tex#bpN:p6:iterative-direct@L130-L130 | V_rD
EDGE: bpN:p4:norm | blueprint-N/parts/p6-normal-form.tex#bpN:p6:iterative-direct@L132-L132 | the unchanged conclusions use O(r,s) and weighted norms
EDGE: bpN:p5:setting | blueprint-N/parts/p6-normal-form.tex#bpN:p6:iterative-direct@L132-L132 | the unchanged conclusions use the bracket, J and the scaled norm
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p6+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: homological_direct (KAM/Nekhoroshev/NormalForm/Homological.lean); IterHyp, iterative_direct_a, iterative_direct_b (KAM/Nekhoroshev/NormalForm/IterativeMap.lean); iterative_direct_c, iterative_direct_d (KAM/Nekhoroshev/NormalForm/IterativeRemainder.lean); iterative_direct_e (KAM/Nekhoroshev/NormalForm/IterativeReal.lean)
LEAN_NOTE: composite of audits N6-2 PASS + N6-5, N6-6, N6-7 PASS WITH NOTES; direct-divisor form (IterHyp carries N-dir)
NOTE: used by Part 11 (bpN:p11:hom, "with Corollary iterative-direct"): inside the N-PARTIAL-CONVEX closure; dropped candidate edges: Remark iterative-special (claimed to hold verbatim, not consumed) and P:bpP:p2:direct (provenance)

NODE: stepN:p6:dir-use
KIND: step
TITLE: Where the old hypotheses enter
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:dir-use@L136-L136
PROOF_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:dir-use@L136-L136
CONTRACT_ID: stepN:p6:dir-use
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: statement of iterative-direct; proofs of homological and iterative
SOURCE_QUANTIFIERS: where (N1), (N2), KLr<=alpha/p enter
SOURCE_CONCLUSION: in hom-def and hom-norm the old hypotheses are used only through Lemma divisor, i.e. the bound |k·omega|>=alpha/q on V_rD for k in Z_K\Lambda; it-gen..it-real use only the conclusions of the homological equation, Parts 4 and 5, and holomorphy/reality of h on V_rD; (N-dir) is exactly that bound
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p6:homological, bpN:p6:iterative, bpN:p6:setting, bpN:p6:divisor, stepN:p6:hom-def, stepN:p6:hom-norm, stepN:p6:it-gen, stepN:p6:it-real, bpN:p4:domains, bpN:p6#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p6:homological | blueprint-N/parts/p6-normal-form.tex#stepN:p6:dir-use@L136-L136 | proof being re-read
EDGE: bpN:p6:iterative | blueprint-N/parts/p6-normal-form.tex#stepN:p6:dir-use@L136-L136 | proof being re-read
EDGE: bpN:p6:setting | blueprint-N/parts/p6-normal-form.tex#stepN:p6:dir-use@L136-L136 | hypotheses (N1), (N2) whose use is localised
EDGE: bpN:p6:divisor | blueprint-N/parts/p6-normal-form.tex#stepN:p6:dir-use@L136-L136 | the only place the old hypotheses enter
EDGE: stepN:p6:hom-def | blueprint-N/parts/p6-normal-form.tex#stepN:p6:dir-use@L136-L136 | uses divisor
EDGE: stepN:p6:hom-norm | blueprint-N/parts/p6-normal-form.tex#stepN:p6:dir-use@L136-L136 | uses divisor
EDGE: stepN:p6:it-gen | blueprint-N/parts/p6-normal-form.tex#stepN:p6:dir-use@L136-L136 | uses only conclusions of the homological equation
EDGE: stepN:p6:it-real | blueprint-N/parts/p6-normal-form.tex#stepN:p6:dir-use@L136-L136 | uses reality of omega from h real
EDGE: bpN:p4:domains | blueprint-N/parts/p6-normal-form.tex#stepN:p6:dir-use@L136-L136 | V_rD or D_{r,s} (including shrunken widths) is used directly
EDGE: bpN:p6#data | blueprint-N/parts/p6-normal-form.tex#stepN:p6:dir-use@L136-L136 | Z_K, q or abar is used directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p6+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: iterative_direct_a, IterHyp (KAM/Nekhoroshev/NormalForm/IterativeMap.lean)
LEAN_NOTE: audit N6-5 PASS WITH NOTES: IterHyp carries the divisor lower bound as the explicit direct-form premise, so homological_direct, IterHyp.canon and the iterative proofs use the hypotheses only through that bound (N6-5-audit-1.md:27; N6-2-audit-1.md:63).
NOTE: -

NODE: stepN:p6:dir-concl
KIND: step
TITLE: Conclusion
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:dir-concl@L137-L137
PROOF_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:dir-concl@L137-L137
CONTRACT_ID: stepN:p6:dir-concl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: dir-use; (N-dir)
SOURCE_QUANTIFIERS: replacement of Lemma divisor
SOURCE_CONCLUSION: replacing Lemma divisor by (N-dir) in hom-def and hom-norm changes nothing else; (N-dir) follows from the original hypotheses (divisor), so the corollary generalises the theorem
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p6:dir-use, bpN:p6:divisor, stepN:p6:hom-def, stepN:p6:hom-norm
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p6:dir-use | blueprint-N/parts/p6-normal-form.tex#stepN:p6:dir-concl@L137-L137 | the two steps identified there
EDGE: bpN:p6:divisor | blueprint-N/parts/p6-normal-form.tex#stepN:p6:dir-concl@L137-L137 | (N-dir) follows from the original hypotheses
EDGE: stepN:p6:hom-def | blueprint-N/parts/p6-normal-form.tex#stepN:p6:dir-concl@L137-L137 | step where divisor is replaced
EDGE: stepN:p6:hom-norm | blueprint-N/parts/p6-normal-form.tex#stepN:p6:dir-concl@L137-L137 | step where divisor is replaced
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p6
REVIEWER: sol-review-N-d
LEAN_STATUS: PROVED
LEAN_REF: iterHyp_of_source (KAM/Nekhoroshev/NormalForm/IterativeMap.lean); homological_direct (KAM/Nekhoroshev/NormalForm/Homological.lean)
LEAN_NOTE: audit N6-5 PASS WITH NOTES, row iterHyp_of_source (:191) derives the direct-form divisor field from the original hypotheses via (divisor ...).2 at N6-5-audit-1.md:35; audit N6-2 row homological_direct N6-2-audit-1.md:63; so the direct-form corollary generalises the theorem.
NOTE: -

NODE: bpN:p6:telescope
KIND: lemma
TITLE: Telescoping
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#bpN:p6:telescope@L148-L150
PROOF_SOURCE: blueprint-N/parts/p6-normal-form.tex#bpN:p6:telescope@L151-L153
CONTRACT_ID: bpN:p6:telescope
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U_0⊃U_1⊃...⊃U_{m+1} subsets of C^{2n}; Phi_i:U_{i+1}->U_i (0<=i<=m); Psi=Phi_0∘...∘Phi_m:U_{m+1}->U_0; for the last assertions every Phi_i holomorphic with (DPhi_i)^T J DPhi_i=J (resp. injective)
SOURCE_QUANTIFIERS: m; U_i; Phi_i; z in U_{m+1}; seminorm mu on C^{2n}
SOURCE_CONCLUSION: mu(Psi(z)-z)<=sum_{i=0}^m sup_{U_{i+1}} mu(Phi_i-id); Psi holomorphic with (DPsi)^T J DPsi=J; Psi injective if every Phi_i is
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p6:tel, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p6:tel | blueprint-N/parts/p6-normal-form.tex#bpN:p6:telescope@L152-L152 | proof step
EDGE: bpN:p5:setting | blueprint-N/parts/p6-normal-form.tex#bpN:p6:telescope@L149-L149 | symplectic matrix J
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p6
REVIEWER: sol-review-N-d
LEAN_STATUS: PROVED
LEAN_REF: chain, telescope (KAM/Nekhoroshev/NormalForm/Telescope.lean)
LEAN_NOTE: audit N6-4 PASS
NOTE: -

NODE: stepN:p6:tel
KIND: step
TITLE: Telescoping
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:tel@L152-L152
PROOF_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:tel@L152-L152
CONTRACT_ID: stepN:p6:tel
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: statement of telescope
SOURCE_QUANTIFIERS: z_{m+1}=z, z_i=Phi_i(z_{i+1})
SOURCE_CONCLUSION: Psi(z)-z=sum (Phi_i-id)(z_{i+1}), triangle inequality; chain rule gives DPsi=prod DPhi_i(z_{i+1}) and (DPsi)^T J DPsi=J by induction; injectivity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p6:ext-chain, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p6:ext-chain | blueprint-N/parts/p6-normal-form.tex#stepN:p6:tel@L152-L152 | chain rule for D(Phi_0∘...∘Phi_m)
EDGE: bpN:p5:setting | blueprint-N/parts/p6-normal-form.tex#stepN:p6:tel@L152-L152 | J, symplectic condition
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p6
REVIEWER: sol-review-N-d
LEAN_STATUS: PROVED
LEAN_REF: telescope (KAM/Nekhoroshev/NormalForm/Telescope.lean)
LEAN_NOTE: audit N6-4 PASS, rows chain, chain_mapsTo, chain_disp, chain_diff_sympl, telescope (Telescope.lean:30-105) at N6-4-audit-1.md:36; step id referenced in N6-4 audit and handoff.
NOTE: -

NODE: bpN:p6:normal-form
KIND: theorem
TITLE: Normal Form Lemma
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#bpN:p6:normal-form@L157-L174
PROOF_SOURCE: blueprint-N/parts/p6-normal-form.tex#bpN:p6:normal-form@L175-L209
CONTRACT_ID: bpN:p6:normal-form
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (N1), (N2), K>0, KLr<=alpha/p (p>1, q=p/(p-1)); s>0; H=h+f with f in O(r,s) of finite norm eps=|f|_{r,s}; (i) eps<=(1/(2^7 q))(alpha r/K); (ii) kappa=2πKs>=6; r_*=r/2, s_*=s/6, c=2qK/(alpha r), g_0=P_Lambda T_K f
SOURCE_QUANTIFIERS: (D,r,K,alpha,L,Lambda,h); p; s; f
SOURCE_CONCLUSION: there are a holomorphic injective Psi:D_{r_*,s_*}->D_{r,s} with (DPsi)^T J DPsi=J and Psi(theta+k,I)=Psi(theta,I)+(k,0), and g, f_* in O(r_*,s_*), g a trig. polynomial in theta with frequencies in Lambda∩Z_K (P_Lambda g=g), such that H∘Psi=h+g+f_* on D_{r_*,s_*} and (a) |g-g_0|_{r_*,s_*}<=16c eps^2 (g=g_0 if N=0 or in case B); (b) |f_*|_{r_*,s_*}<=e^{-2πKs/6}eps=e^{-kappa/6}eps; (c) |Pi_I Psi-I|_inf<=qK eps/alpha (=c r eps/2) and |Pi_theta Psi-theta|_inf<=10q eps/(2πalpha r); (d) if Lambda=-Lambda and h,f real on real points then g, f_* real on real points and Psi maps real points to real points
CONSTANT_SCOPE: Psi, g, f_* are constructed from (h,f,K,alpha,L,Lambda,p) and (r,s); r_*, s_*, c depend only on (r,s,K,alpha,q)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p6:nf-first, stepN:p6:nf-case, stepN:p6:nf-N, stepN:p6:nf-induct, stepN:p6:nf-concl, stepN:p6:nf-disp, stepN:p6:nf-real, bpN:p6:setting, bpN:p6#data, bpN:p4:norm, bpN:p4:domains, bpN:p4:projections, bpN:p5:setting, bpN:p6:normal-form#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p6:nf-first | blueprint-N/parts/p6-normal-form.tex#bpN:p6:normal-form@L178-L178 | proof step
EDGE: stepN:p6:nf-case | blueprint-N/parts/p6-normal-form.tex#bpN:p6:normal-form@L180-L180 | proof step
EDGE: stepN:p6:nf-N | blueprint-N/parts/p6-normal-form.tex#bpN:p6:normal-form@L186-L186 | proof step
EDGE: stepN:p6:nf-induct | blueprint-N/parts/p6-normal-form.tex#bpN:p6:normal-form@L191-L191 | proof step
EDGE: stepN:p6:nf-concl | blueprint-N/parts/p6-normal-form.tex#bpN:p6:normal-form@L200-L200 | proof step
EDGE: stepN:p6:nf-disp | blueprint-N/parts/p6-normal-form.tex#bpN:p6:normal-form@L204-L204 | proof step
EDGE: stepN:p6:nf-real | blueprint-N/parts/p6-normal-form.tex#bpN:p6:normal-form@L208-L208 | proof step
EDGE: bpN:p6:setting | blueprint-N/parts/p6-normal-form.tex#bpN:p6:normal-form@L158-L158 | hypotheses (N1), (N2)
EDGE: bpN:p6#data | blueprint-N/parts/p6-normal-form.tex#bpN:p6:normal-form@L158-L159 | K, q, kappa=2πKs, abar, Z_K
EDGE: bpN:p4:norm | blueprint-N/parts/p6-normal-form.tex#bpN:p6:normal-form@L158-L158 | class O(r,s), norm
EDGE: bpN:p4:domains | blueprint-N/parts/p6-normal-form.tex#bpN:p6:normal-form@L162-L162 | domains D_{r_*,s_*}, D_{r,s}
EDGE: bpN:p4:projections | blueprint-N/parts/p6-normal-form.tex#bpN:p6:normal-form@L160-L160 | g_0=P_Lambda T_K f
EDGE: bpN:p5:setting | blueprint-N/parts/p6-normal-form.tex#bpN:p6:normal-form@L162-L162 | J and the symplectic condition
EDGE: bpN:p6:normal-form#data | blueprint-N/parts/p6-normal-form.tex#bpN:p6:normal-form@L176-L176 | the proof fixes the iteration data used in its steps
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p6+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: normal_form (KAM/Nekhoroshev/NormalForm/NormalForm.lean)
LEAN_NOTE: audit N6-8b PASS WITH NOTES (with N6-8a Arith/Steps interface PASS)
NOTE: sourcegap at L173 (Pöschel prints e^{Ks/6} for e^{-Ks/6}) is filled by Case B of nf-case; dropped candidate edges: composition, iterative (source provenance only), deviations (remark)

NODE: stepN:p6:nf-first
KIND: step
TITLE: Step 0: hypotheses of the Iterative Lemma
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-first@L178-L178
PROOF_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-first@L178-L178
CONTRACT_ID: stepN:p6:nf-first
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: statement of normal-form; (i), (ii)
SOURCE_QUANTIFIERS: rho_0=r/8, sigma_0=s/6
SOURCE_CONCLUSION: 2rho_0<r, 2sigma_0<s, KLr<=alpha/p; eps<=abar rho_0 sigma_0/(16q); y_0:=q eps/(abar rho_0 sigma_0)<=1/16 so u<=1/4 and the Iterative Lemma applies; kappa/6=2πK sigma_0>=1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p6:setting, bpN:p6#data, bpN:p6:normal-form#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p6:setting | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-first@L178-L178 | KLr<=alpha/p carried by the setting
EDGE: bpN:p6#data | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-first@L178-L178 | kappa, abar, q
EDGE: bpN:p6:normal-form#data | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-first@L178-L178 | V_i, f_i, g_i, Phi_i and/or eps_i use the indexing fixed at L176
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p6+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: normal_form (KAM/Nekhoroshev/NormalForm/NormalForm.lean)
LEAN_NOTE: audit N6-8a PASS WITH NOTES, row nf-first iterU_first (ArithBase:104: u0<=1/16 from (i),(ii)) at N6-8a-audit-1.md:65 and nfRho/nfSig rows; carrier normal_form (N6-8b audit N6-8b-audit-1.md:49).
NOTE: -

NODE: stepN:p6:nf-case
KIND: step
TITLE: Step 0: two cases
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-case@L180-L184
PROOF_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-case@L180-L184
CONTRACT_ID: stepN:p6:nf-case
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: nf-first; Iterative Lemma (d) with g=0, delta=eps
SOURCE_QUANTIFIERS: Case A: e^{-kappa/6}<=y_0; Case B: e^{-kappa/6}>y_0
SOURCE_CONCLUSION: |f_1|<=(1-2y_0)^{-1}((2/e)y_0+e^{-kappa/6})eps, (1-2y_0)^{-1}<=8/7; Case A: eps_1<=(16/7)y_0 eps<=...<=eps/kappa<=eps/4 (6.1); Case B: repeat with losses (r/4,s/3), |f_1|_{r/2,s/3}<=e^{-kappa/6}eps, stop with Psi=Phi_0', g=g_0, f_*=f_1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p6:iterative, stepN:p6:nf-first, bpN:p6:ext-numerics, bpN:p6#data, bpN:p6:normal-form#data, bpN:p4:norm, bpN:p4:domains, bpN:p6:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p6:iterative | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-case@L180-L184 | (d) with g=0 (¦g¦_*=0), and the repeated application with doubled losses in case B
EDGE: stepN:p6:nf-first | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-case@L180-L180 | y_0<=1/16, hypotheses of the first step
EDGE: bpN:p6:ext-numerics | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-case@L180-L184 | 8/7, 2/e<1, 32/31 type numerics, e^{-2kappa/6}<=e^{-1}e^{-kappa/6}
EDGE: bpN:p6#data | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-case@L180-L180 | kappa, abar
EDGE: bpN:p6:normal-form#data | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-case@L180-L180 | V_i, f_i, g_i, Phi_i and/or eps_i use the indexing fixed at L176
EDGE: bpN:p4:norm | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-case@L184-L184 | direct use of domains, weighted norms/restriction, the decomposed norm, or the symplectic convention at this stage
EDGE: bpN:p4:domains | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-case@L184-L184 | direct use of domains, weighted norms/restriction, the decomposed norm, or the symplectic convention at this stage
EDGE: bpN:p6:setting | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-case@L180-L180 | the decomposed norm ¦g¦_* is used with g=0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p6+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: normal_form (KAM/Nekhoroshev/NormalForm/NormalForm.lean)
LEAN_NOTE: audit N6-8a PASS WITH NOTES, rows nf-case: nfEps1, nfBound, nfBound_caseA, nfBound_caseB, eps1_le_div, eps1_le_quarter at N6-8a-audit-1.md:71 and N6-8a-audit-1.md:42; N6-8b rows nfConcl_caseB (N6-8b-audit-1.md:64).
NOTE: -

NODE: stepN:p6:nf-N
KIND: step
TITLE: Number of steps
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-N@L186-L189
PROOF_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-N@L186-L189
CONTRACT_ID: stepN:p6:nf-N
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: nf-first, nf-case (6.1)
SOURCE_QUANTIFIERS: N=floor(kappa/(12 ln2)); rho_i, sigma_i, r_i, s_i
SOURCE_CONCLUSION: kappa>=12ln2 N>8N; if N=0 stop with Psi=Phi_0, g=g_0, f_*=f_1, |f_*|<=eps/4<=e^{-kappa/6}eps; for N>=1: rho=r/(8N), sigma=s/(4N), r_{N+1}=r_*, s_{N+1}=s_*, e^{-2πK sigma}<=1/8, rho sigma=rs/(32N^2), (6.2) eps_1<=abar rho sigma/(2^8 q)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p6:ext-numerics, stepN:p6:nf-case, stepN:p6:nf-first, bpN:p6#data, bpN:p6:normal-form#data, bpN:p4:norm, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p6:ext-numerics | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-N@L186-L189 | 12 ln2>8, e^{-3ln2}=1/8
EDGE: stepN:p6:nf-case | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-N@L186-L189 | (6.1) eps_1<=eps/kappa<=eps/4
EDGE: stepN:p6:nf-first | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-N@L186-L186 | r_1=3r/4, s_1=2s/3 starting widths
EDGE: bpN:p6#data | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-N@L186-L188 | kappa=2πKs, abar
EDGE: bpN:p6:normal-form#data | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-N@L186-L186 | V_i, f_i, g_i, Phi_i and/or eps_i use the indexing fixed at L176
EDGE: bpN:p4:norm | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-N@L186-L186 | direct use of domains, weighted norms/restriction, the decomposed norm, or the symplectic convention at this stage
EDGE: bpN:p4:domains | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-N@L186-L186 | direct use of domains, weighted norms/restriction, the decomposed norm, or the symplectic convention at this stage
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p6+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: normal_form (KAM/Nekhoroshev/NormalForm/NormalForm.lean)
LEAN_NOTE: audit N6-8a PASS WITH NOTES, rows nf-N: nfSteps/nfR/nfS, quarter_lt_exp, floor_facts, schedule rows nfR_succ_closed...nfS_sixth_le, eps_le_sixtwo, eps1_sixtwo at N6-8a-audit-1.md:44 to N6-8a-audit-1.md:101; nfSteps in N6-8b N6-8b-audit-1.md:36.
NOTE: -

NODE: stepN:p6:nf-induct
KIND: step
TITLE: Induction
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-induct@L191-L198
PROOF_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-induct@L191-L198
CONTRACT_ID: stepN:p6:nf-induct
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: nf-N: rho, sigma, (6.1), (6.2)
SOURCE_QUANTIFIERS: 1<=i<=N
SOURCE_CONCLUSION: step i admissible and eps_{i+1}<=eps_i/4, so eps_i<=4^{1-i}eps_1 and |g_i-g_{i-1}|<=eps_i; |g_{i-1}|_*<=(1/2)(eps_{i-1}+...+eps_1)+eps/N<=abar rho sigma/(2^4 q); eps_{i+1}<=(128/127)(1/16+1/256+1/8)eps_i<eps_i/4
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p6:iterative, bpN:p4:projections, bpN:p6:setting, stepN:p6:nf-N, stepN:p6:nf-case, bpN:p6:ext-numerics, bpN:p4:norm, bpN:p6#data, bpN:p6:normal-form#data, bpN:p4:domains, bpN:p4:norm#monotone
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p6:iterative | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-induct@L197-L197 | (d) with delta=eps_i
EDGE: bpN:p4:projections | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-induct@L191-L191 | ¦P_Lambda T_K f_i¦<=¦f_i¦
EDGE: bpN:p6:setting | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-induct@L194-L194 | ¦g_{i-1}¦_* weights for the decomposition g_0+sum(g_j-g_{j-1})
EDGE: stepN:p6:nf-N | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-induct@L192-L193 | rho, sigma, N, r_i, s_i, (6.2)
EDGE: stepN:p6:nf-case | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-induct@L192-L192 | (6.1) eps_1<=eps/4
EDGE: bpN:p6:ext-numerics | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-induct@L195-L197 | sum 4^{1-i}=4/3, 128/127, 2/e<1
EDGE: bpN:p4:norm | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-induct@L194-L194 | norms of the terms
EDGE: bpN:p6#data | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-induct@L193-L193 | K, abar, q
EDGE: bpN:p6:normal-form#data | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-induct@L191-L191 | V_i, f_i, g_i, Phi_i and/or eps_i use the indexing fixed at L176
EDGE: bpN:p4:domains | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-induct@L194-L194 | direct use of domains, weighted norms/restriction, the decomposed norm, or the symplectic convention at this stage
EDGE: bpN:p4:norm#monotone | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-induct@L194-L194 | direct use of domains, weighted norms/restriction, the decomposed norm, or the symplectic convention at this stage
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p6+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: normal_form (KAM/Nekhoroshev/NormalForm/NormalForm.lean)
LEAN_NOTE: audit N6-8a PASS WITH NOTES, rows nf-induct: nfB, induct_step (49/254<1/4), star_sum_le, w0_le, star_small at N6-8a-audit-1.md:41 to N6-8a-audit-1.md:108.
NOTE: -

NODE: stepN:p6:nf-concl
KIND: step
TITLE: Conclusion of the construction
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-concl@L200-L202
PROOF_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-concl@L200-L202
CONTRACT_ID: stepN:p6:nf-concl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: nf-induct, nf-N, nf-case; Lemma telescope
SOURCE_QUANTIFIERS: Psi=Phi_0∘...∘Phi_N, g=g_N, f_*=f_{N+1} on V_{N+1}=D_{r_*,s_*}
SOURCE_CONCLUSION: H∘Psi=h+g+f_*; g finite sum of trig polynomials with frequencies in Lambda∩Z_K; Psi symplectic periodic injective; (b) |f_*|<=e^{-kappa/6}eps; (a) |g-g_0|<=(4/3)eps_1<=16c eps^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p6:telescope, bpN:p6:iterative, stepN:p6:nf-induct, stepN:p6:nf-N, stepN:p6:nf-case, bpN:p4:projections, bpN:p6:ext-numerics, bpN:p6#data, bpN:p6:normal-form#data, bpN:p4:domains, bpN:p4:norm, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p6:telescope | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-concl@L200-L200 | holomorphy, symplecticity and injectivity of the composition
EDGE: bpN:p6:iterative | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-concl@L200-L200 | (a) periodicity of each Phi_i, (c) H_{i+1}=H_i∘Phi_i
EDGE: stepN:p6:nf-induct | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-concl@L200-L202 | eps_i<=4^{1-i}eps_1 and sums
EDGE: stepN:p6:nf-N | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-concl@L201-L201 | N+1>kappa/(12 ln2), kappa>8N
EDGE: stepN:p6:nf-case | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-concl@L202-L202 | (6.1)
EDGE: bpN:p4:projections | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-concl@L200-L200 | g_i-g_{i-1}=P_Lambda T_K f_i trig. polynomials with frequencies in Lambda∩Z_K
EDGE: bpN:p6:ext-numerics | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-concl@L201-L201 | e^{-(N+1)2ln2}<e^{-kappa/6}
EDGE: bpN:p6#data | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-concl@L202-L202 | abar s=alpha kappa/K
EDGE: bpN:p6:normal-form#data | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-concl@L200-L200 | V_i, f_i, g_i, Phi_i and/or eps_i use the indexing fixed at L176
EDGE: bpN:p4:domains | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-concl@L200-L200 | direct use of domains, weighted norms/restriction, the decomposed norm, or the symplectic convention at this stage
EDGE: bpN:p4:norm | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-concl@L200-L200 | direct use of domains, weighted norms/restriction, the decomposed norm, or the symplectic convention at this stage
EDGE: bpN:p5:setting | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-concl@L200-L200 | direct use of domains, weighted norms/restriction, the decomposed norm, or the symplectic convention at this stage
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p6+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: normal_form (KAM/Nekhoroshev/NormalForm/NormalForm.lean)
LEAN_NOTE: audit N6-8a/8b PASS WITH NOTES, rows nf-concl: final_b, concl_a (N6-8a N6-8a-audit-1.md:75, N6-8a-audit-1.md:109); chain_translate, coeff_homRes, coeff_sum_eq_zero, nf_coeff_g, nfConcl_caseA (N6-8b N6-8b-audit-1.md:52 to N6-8b-audit-1.md:63).
NOTE: -

NODE: stepN:p6:nf-disp
KIND: step
TITLE: (c) Displacement
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-disp@L204-L206
PROOF_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-disp@L204-L206
CONTRACT_ID: stepN:p6:nf-disp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: nf-concl; Iterative Lemma (b)
SOURCE_QUANTIFIERS: Pi_I Psi-I, Pi_theta Psi-theta
SOURCE_CONCLUSION: Case A: |Pi_I Psi-I|_inf<=(q K eps/(e alpha))·1.17<=qK eps/alpha and |Pi_theta Psi-theta|_inf<=10q eps/abar r; Case B: bounds smaller by factor 1/2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p6:telescope, bpN:p6:iterative, stepN:p6:nf-case, stepN:p6:nf-N, stepN:p6:nf-induct, bpN:p6:ext-numerics, bpN:p6#data, bpN:p6:normal-form#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p6:telescope | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-disp@L204-L204 | displacement of a composition with seminorms ¦Pi_I.¦, ¦Pi_theta.¦
EDGE: bpN:p6:iterative | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-disp@L204-L204 | (b) per-step displacement bounds
EDGE: stepN:p6:nf-case | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-disp@L205-L206 | eps_1<=eps/kappa, case B displacement
EDGE: stepN:p6:nf-N | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-disp@L206-L206 | 1/(abar sigma)=4NK/(alpha kappa), N<=kappa/(12 ln2)
EDGE: stepN:p6:nf-induct | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-disp@L205-L205 | eps_i bounds
EDGE: bpN:p6:ext-numerics | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-disp@L206-L206 | 12 ln2>8 and ln2 numerics
EDGE: bpN:p6#data | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-disp@L206-L206 | kappa, abar
EDGE: bpN:p6:normal-form#data | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-disp@L204-L204 | V_i, f_i, g_i, Phi_i and/or eps_i use the indexing fixed at L176
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p6+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: normal_form (KAM/Nekhoroshev/NormalForm/NormalForm.lean)
LEAN_NOTE: audit N6-8a PASS WITH NOTES, rows nf-disp (c): disp_I, disp_theta, disp_B (ArithDisp:32,96,150) at N6-8a-audit-1.md:76 to N6-8a-audit-1.md:78; N6-8b rows fstSeminorm, sndSeminorm, nfConcl_caseA.
NOTE: -

NODE: stepN:p6:nf-real
KIND: step
TITLE: (d) Reality
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-real@L208-L208
PROOF_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-real@L208-L208
CONTRACT_ID: stepN:p6:nf-real
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Lambda=-Lambda; h,f real on real points
SOURCE_QUANTIFIERS: steps i
SOURCE_CONCLUSION: each step preserves reality (Iterative Lemma (e)); g_i, f_i, H_i real and Phi_i real-point-preserving; compositions preserve real points
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p6:iterative, stepN:p6:nf-concl, bpN:p6:normal-form#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p6:iterative | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-real@L208-L208 | (e) reality at each step
EDGE: stepN:p6:nf-concl | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-real@L208-L208 | Psi=Phi_0∘...∘Phi_N, g=g_N, f_*=f_{N+1}
EDGE: bpN:p6:normal-form#data | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nf-real@L208-L208 | V_i, f_i, g_i, Phi_i and/or eps_i use the indexing fixed at L176
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p6+sol-review-N-d
REVIEWER: sol-delta-N-d
LEAN_STATUS: PROVED
LEAN_REF: normal_form (KAM/Nekhoroshev/NormalForm/NormalForm.lean)
LEAN_NOTE: audit N6-8a PASS WITH NOTES, row nf-real (d) nf_real (StepsCaseB:41) at N6-8a-audit-1.md:35; N6-8b row chain_real (N6-8b-audit-1.md:53).
NOTE: -

NODE: bpN:p6:nonresonant-case
KIND: proposition
TITLE: No transformation for small $Ks$
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#bpN:p6:nonresonant-case@L221-L227
PROOF_SOURCE: blueprint-N/parts/p6-normal-form.tex#bpN:p6:nonresonant-case@L228-L230
CONTRACT_ID: bpN:p6:nonresonant-case
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: H=h+f on D_{r,s}; f in O(r,s) with finite norm eps; kappa=2πKs<6
SOURCE_QUANTIFIERS: h; f; r; s; K
SOURCE_CONCLUSION: with Psi=id, g=0, f_*=f: H∘Psi=h+g+f_* on D_{r,s}, |Psi-id|=0, |f_*|_{r,s}=eps<=e·e^{-kappa/6}eps, and g=0=P_Lambda g is in Lambda-normal form for every Lambda; no nonresonance, convexity or smallness hypothesis is used
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p6:nr-triv, bpN:p4:norm, bpN:p6#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p6:nr-triv | blueprint-N/parts/p6-normal-form.tex#bpN:p6:nonresonant-case@L229-L229 | proof step
EDGE: bpN:p4:norm | blueprint-N/parts/p6-normal-form.tex#bpN:p6:nonresonant-case@L222-L222 | class O(r,s) and the norm ¦f¦_{r,s}
EDGE: bpN:p6#data | blueprint-N/parts/p6-normal-form.tex#bpN:p6:nonresonant-case@L222-L222 | kappa=2πKs
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p6
REVIEWER: sol-review-N-d
LEAN_STATUS: PROVED
LEAN_REF: nonresonant_case (KAM/Nekhoroshev/NormalForm/NormalForm.lean)
LEAN_NOTE: audit N6-8b PASS WITH NOTES
NOTE: sourcegap at L226 (the bound |f_*|<=e^{-kappa/6}eps is false for kappa<6; the correct bound is e e^{-kappa/6}eps) is the stated conclusion; used by Part 7 (nr-caseB). The remark text says Part 7 does not need it; Part 7 step nr-caseB cites it for Psi=id, g=0, f_*=f; dropped candidate edge: Remark p7:factor-e (provenance)

NODE: stepN:p6:nr-triv
KIND: step
TITLE: Trivial
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:nr-triv@L229-L229
PROOF_SOURCE: blueprint-N/parts/p6-normal-form.tex#stepN:p6:nr-triv@L229-L229
CONTRACT_ID: stepN:p6:nr-triv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: statement of nonresonant-case
SOURCE_QUANTIFIERS: kappa<=6
SOURCE_CONCLUSION: Psi=id, g=0, |f_*|=eps and 1<=e^{1-kappa/6} for kappa<=6
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p6#data, bpN:p4:norm
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p6#data | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nr-triv@L229-L229 | kappa
EDGE: bpN:p4:norm | blueprint-N/parts/p6-normal-form.tex#stepN:p6:nr-triv@L229-L229 | norm ¦f¦_{r,s}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p6
REVIEWER: sol-review-N-d
LEAN_STATUS: PROVED
LEAN_REF: nonresonant_case (KAM/Nekhoroshev/NormalForm/NormalForm.lean)
LEAN_NOTE: audit N6-8b PASS WITH NOTES, row nonresonant-case / nr-triv nonresonant_case (NormalForm:139) at N6-8b-audit-1.md:50.
NOTE: -

NODE: bpN:p6#data
KIND: definition
TITLE: Notation of Part 6 (Z_K, q, abar, kappa)
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#bpN:p6#data@L11-L16
PROOF_SOURCE: -
CONTRACT_ID: bpN:p6#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data: n; real K>=0; p>1; alpha>0; s>0; Lambda subset Z^n)
SOURCE_QUANTIFIERS: n; K; p; alpha; s
SOURCE_CONCLUSION: defines Z_K={k in Z^n: |k|_1<=K}; omega=∂_I h; q=p/(p-1) (so 1/p+1/q=1); abar=2πα; kappa=2πKs; the two Pöschel dictionaries (symplectic scaling; fixed-action Hamiltonian scaling) are recorded for comparison only
CONSTANT_SCOPE: p>1 arbitrary (Pöschel takes q=9, p=9/8; nothing in Part 6 depends on that choice); abar, kappa are abbreviations, not constants chosen later
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p6
REVIEWER: sol-review-N-d
LEAN_STATUS: PROVED
LEAN_REF: zBall, freq, dotC, conjExp (KAM/Nekhoroshev/NormalForm/Setting.lean)
LEAN_NOTE: audit N6-1 PASS
NOTE: section-data node for coverage item p6:prose-L11-L16 (SPEC table); used by symbol in the setting, divisor, homological equation, Iterative Lemma, Normal Form Lemma and nonresonant case

NODE: bpN:p6:normal-form#data
KIND: definition
TITLE: Normal-form iteration indexing
STATEMENT_SOURCE: blueprint-N/parts/p6-normal-form.tex#bpN:p6:normal-form@L176-L176
PROOF_SOURCE: -
CONTRACT_ID: bpN:p6:normal-form#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: data of the Normal Form Lemma; conditional iteration prescription (each step must separately be shown admissible)
SOURCE_QUANTIFIERS: stage i and chosen losses rho_i, sigma_i
SOURCE_CONCLUSION: fixes abar=2πalpha, kappa=2πKs; abar s=alpha kappa/K and K>=3/(πs); fixes V_i=D_{r_i,s_i}, f_0=f, g_{-1}=0, H_i=h+g_{i-1}+f_i; an admissible Iterative-Lemma step produces Phi_i:V_{i+1}->V_i, g_i=g_{i-1}+P_Lambda T_K f_i and f_{i+1}, r_{i+1}=r_i-2rho_i, s_{i+1}=s_i-2sigma_i; eps_i=|f_i|_{V_i}, eps_0=eps; Phi_i maps V_{i+1} into D_{r_i-3rho_i/2,s_i-3sigma_i/2} and is injective on V_{i+1}
CONSTANT_SCOPE: indexing and definitions only; no admissibility asserted
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p4:domains, bpN:p4:norm, bpN:p4:projections, bpN:p6:iterative, bpN:p6#data, bpN:p6:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p4:domains | blueprint-N/parts/p6-normal-form.tex#bpN:p6:normal-form@L176-L176 | V_i and the shrunken domains
EDGE: bpN:p4:norm | blueprint-N/parts/p6-normal-form.tex#bpN:p6:normal-form@L176-L176 | eps_i=¦f_i¦_{V_i}
EDGE: bpN:p4:projections | blueprint-N/parts/p6-normal-form.tex#bpN:p6:normal-form@L176-L176 | g_i uses P_Lambda T_K f_i
EDGE: bpN:p6:iterative | blueprint-N/parts/p6-normal-form.tex#bpN:p6:normal-form@L176-L176 | specifies the output of an admissible step, without claiming its hypotheses
EDGE: bpN:p6#data | blueprint-N/parts/p6-normal-form.tex#bpN:p6:normal-form@L176-L176 | abar and kappa are the Part-6 normalization data, used in the opening identities
EDGE: bpN:p6:setting | blueprint-N/parts/p6-normal-form.tex#bpN:p6:normal-form@L176-L176 | the inherited Normal Form data fixes h and the resonant setting for H_i=h+g_{i-1}+f_i
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: new+sol-delta-N-d
REVIEWER: sol-delta2-N-d
LEAN_STATUS: PROVED
LEAN_REF: nfSteps (KAM/Nekhoroshev/NormalForm/NormalFormCaseA.lean)
LEAN_NOTE: audit N6-8b PASS WITH NOTES
NOTE: section/construction data used without references throughout the normal-form proof; separated from the parent to avoid a parent/step cycle.

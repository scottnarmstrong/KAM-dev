NODE: bpW:w3:ext-multilinear
KIND: external
TITLE: Multilinear maps
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:ext-multilinear@L42-L48
PROOF_SOURCE: -
CONTRACT_ID: bpW:w3:ext-multilinear
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: continuous multilinear maps between Banach spaces form a Banach space under the operator norm; inserting a continuous multilinear map into a slot of another, or composing with continuous linear maps, gives a continuous multilinear map of norm at most the product; the diagonal P(w) = M(w,...,w) of a continuous d-linear M is C^infinity with DP(w)v = sum_i M(w,..,v (slot i),..,w)
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
REVIEWER: sol-review-W-w3
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:ext-series
KIND: external
TITLE: Power series
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:ext-series@L49-L59
PROOF_SOURCE: -
CONTRACT_ID: bpW:w3:ext-series
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: if (M_n) are continuous n-linear with sum ¦¦M_n¦¦ r^n < infinity then f(w) = sum M_n(w,..,w) has this power series on the open ball of radius r, is analytic there, derivative termwise; finite sums, compositions and continuous multilinear images of analytic maps are analytic; A -> A^{-1} is analytic on the units of a Banach algebra; the derivative of an analytic map is analytic; C-analytic implies R-analytic; a FormalMultilinearSeries carries explicit zero coefficients
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
REVIEWER: sol-review-W-w3
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:ext-tsum
KIND: external
TITLE: Termwise differentiation
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:ext-tsum@L60-L68
PROOF_SOURCE: -
CONTRACT_ID: bpW:w3:ext-tsum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: termwise differentiation of sum f_k on an open convex set under sum sup ¦¦Df_k¦¦ < infinity and convergence at a point; absolutely summable families may be regrouped along any partition; for a continuous multilinear B and absolutely summable families, B(sum a^1,..,sum a^r) = sum B(a^1_{i_1},..,a^r_{i_r}) absolutely (Cauchy products)
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
REVIEWER: sol-review-W-w3
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:ext-mvt
KIND: external
TITLE: Mean value inequality; zero derivative
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:ext-mvt@L69-L72
PROOF_SOURCE: -
CONTRACT_ID: bpW:w3:ext-mvt
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: mean value inequality ¦¦f(y) - f(x)¦¦ <= M ¦¦y - x¦¦ on a convex set with ¦¦Df¦¦ <= M; a differentiable function on an interval with vanishing derivative is constant
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
REVIEWER: sol-review-W-w3
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:ext-integral
KIND: external
TITLE: Integrals in a parameter
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:ext-integral@L73-L82
PROOF_SOURCE: -
CONTRACT_ID: bpW:w3:ext-integral
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: for Y : [0,1] x U -> V continuous, differentiable in w with D_w Y continuous and bounded, w -> int_0^1 Y(t,w) dt is differentiable with derivative int D_w Y (complex differentiable over C); the fundamental theorem of calculus for C^1 maps [0,1] -> V; continuous linear maps commute with the Bochner integral; ¦¦int Y¦¦ <= int ¦¦Y¦¦; termwise integration of sum g_j with sup ¦¦g_j¦¦ <= c_j, sum c_j < infinity
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
REVIEWER: sol-review-W-w3
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:ext-neumann
KIND: external
TITLE: Neumann series
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:ext-neumann@L83-L86
PROOF_SOURCE: -
CONTRACT_ID: bpW:w3:ext-neumann
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: if A is a bounded operator on a Banach space with ¦¦A - I¦¦ <= 1/2 then A is invertible, ¦¦A^{-1}¦¦ <= 2, ¦¦A^{-1} - I¦¦ <= 2¦¦A - I¦¦, and A^{-1} = sum_{n>=0} (I - A)^n absolutely
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
REVIEWER: sol-review-W-w3
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:space
KIND: definition
TITLE: Two-sided coordinate space
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:space@L108-L116
PROOF_SOURCE: -
CONTRACT_ID: bpW:w3:space
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; typing data a >= 0, r in R
SOURCE_QUANTIFIERS: a, r
SOURCE_CONCLUSION: defines W_{a,r} = complex families (w_l)_{l in Z\0} with ¦¦w¦¦_{a,r}^2 = sum_{l != 0} ¦l¦^{2r} e^{2a¦l¦} ¦w_l¦^2 < infinity; W = W_{a,p}, W+ = W_{a,p+1} (norms ¦¦.¦¦, ¦¦.¦¦_+); tilde w (¦l¦ <= 2) and hat w (¦l¦ >= 3); lambda'_l = sgn(l) lambda_¦l¦; Lean carrier lp (Bool x PNat -> C) 2 in weighted coordinates
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3#data, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:space@L111-L111 | W = W_{a,p} with the standing a, p
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:space@L113-L113 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.BirkIdx, KAM.Wave.BirkSpace, KAM.Wave.birkCoord, KAM.Wave.birkEmbed, KAM.Wave.birkEmbed_injective, KAM.Wave.norm_birkEmbed_le, KAM.Wave.birkCoord_birkEmbed, KAM.Wave.birkRho, KAM.Wave.birkCoord_birkRho, KAM.Wave.birkSgn, KAM.Wave.birkLam, KAM.Wave.lpDiagCLM, KAM.Wave.birkNormalPart (KAM/Wave/Birkhoff/Space.lean, KAM/Wave/Birkhoff/QuartNormal.lean)
LEAN_NOTE: definition formalized by W3-SETTING; W3-SETTING-DIVF audit 1 PASS (space row); carrier lp (Bool x PNat -> C) 2 in weighted coordinates, W+ read at weight p+1
NOTE: -

NODE: bpW:w3:coords
KIND: lemma
TITLE: Complex coordinates and real structure
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:coords@L119-L128
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:coords@L130-L136
CONTRACT_ID: bpW:w3:coords
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; E^C = l^{a,p}_C x l^{a,p}_C with the max norm; Z : E^C -> W, (Zx)_j = (q_j + i p_j)/sqrt2, (Zx)_{-j} = (q_j - i p_j)/sqrt2
SOURCE_QUANTIFIERS: for all x in E^C, w in W
SOURCE_CONCLUSION: Z is a C-linear bijection with ¦¦x¦¦_E <= ¦¦Zx¦¦ <= sqrt2 ¦¦x¦¦_E, mapping E^C_{a,p+1} onto W+ with the same bounds; rho(w)_l = conj(w_{-l}) is a conjugate-linear isometric involution of W and W+; Z maps the real E_{a,p} bijectively onto W_R = {rho w = w}; on real points w_j = z_j, w_{-j} = zbar_j, w_j w_{-j} = ¦z_j¦^2 = I_j
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:space, bpW:w0:z, bpW:w0:actions, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:space | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:coords@L121-L121 | the space W
EDGE: bpW:w0:z | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:coords@L127-L127 | the complex coordinates z_j
EDGE: bpW:w0:actions | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:coords@L127-L127 | I_j = ¦z_j¦^2
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:coords@L119-L128 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.birkZ, KAM.Wave.birkZinv, KAM.Wave.birkZEquiv, KAM.Wave.norm_le_norm_birkZ, KAM.Wave.norm_birkZ_le, KAM.Wave.norm_birkZinv_le, KAM.Wave.birkCoord_birkZ_true, KAM.Wave.birkCoord_birkZ_false, KAM.Wave.birkCoord_mul_birkZ, KAM.Wave.birkRho_birkZ_real, KAM.Wave.exists_birkZ_of_birkRho_eq, KAM.Wave.birkReal, KAM.Wave.birkReal_injective (KAM/Wave/Birkhoff/Coords.lean)
LEAN_NOTE: W3-SETTING-DIVF audit 1 PASS
NOTE: -

NODE: bpW:w3:omega
KIND: lemma
TITLE: Symplectic form
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:omega@L139-L145
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:omega@L147-L151
CONTRACT_ID: bpW:w3:omega
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}
SOURCE_QUANTIFIERS: for all w, w' in W; x, x' real in E
SOURCE_CONCLUSION: Omega(w,w') = i sum_{l != 0} sgn(l) w_l w'_{-l} is continuous antisymmetric bilinear on W, ¦Omega(w,w')¦ <= ¦¦w¦¦ ¦¦w'¦¦, nondegenerate (Omega(zeta,e_{-l}) = i sgn(l) zeta_l); Omega(Zx,Zx') = sum (q_j p'_j - p_j q'_j) (the form sum dq ^ dp); Omega(rho w, rho w') = conj Omega(w,w')
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:space, bpW:w3:coords, bpW:w0:eqmotion, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:space | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:omega@L140-L140 | the space W and its norm
EDGE: bpW:w3:coords | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:omega@L149-L149 | the inverse formulas of Z
EDGE: bpW:w0:eqmotion | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:omega@L144-L144 | the symplectic form sum dq_j ^ dp_j
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:omega@L139-L145 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.birkOmega, KAM.Wave.norm_birkOmega_le, KAM.Wave.birkOmega_antisymm, KAM.Wave.birkOmega_unit_neg, KAM.Wave.birkOmega_nondegenerate, KAM.Wave.birkOmega_birkZ, KAM.Wave.birkOmega_birkZ_real, KAM.Wave.birkOmega_birkRho (KAM/Wave/Birkhoff/Omega.lean)
LEAN_NOTE: W3-SETTING-DIVF audit 1 PASS
NOTE: -

NODE: bpW:w3:hamfield-def
KIND: definition
TITLE: Hamiltonian field; one-smoothing holomorphic class
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:hamfield-def@L154-L162
PROOF_SOURCE: -
CONTRACT_ID: bpW:w3:hamfield-def
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; U subset W open, P : U -> C complex differentiable
SOURCE_QUANTIFIERS: U, P
SOURCE_CONCLUSION: defines X_P as the map with DP(w)v = Omega(X_P(w),v) for all w in U, v in W (unique, X_P(w)_l = -i sgn(l) DP(w) e_{-l}); P real iff P(rho w) = conj P(w) on U = rho U (then X_P o rho = rho o X_P); the class A(U) of real P analytic on U whose Hamiltonian field exists, takes values in W+, and is analytic U -> W+; analytic maps are holomorphic (Definition bpW:w1:holomorphic)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:omega, bpW:w3:coords, bpW:w1:holomorphic, bpW:w1:ext-analytic, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:omega | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:hamfield-def@L157-L157 | uniqueness by nondegeneracy; the formula for X_P
EDGE: bpW:w3:coords | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:hamfield-def@L158-L158 | the involution rho
EDGE: bpW:w1:holomorphic | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:hamfield-def@L161-L161 | holomorphic maps
EDGE: bpW:w1:ext-analytic | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:hamfield-def@L161-L161 | analytic maps are Frechet differentiable, hence holomorphic
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:hamfield-def@L154-L162 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w3+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.IsBirkHamFieldW, KAM.Wave.birkFieldW_eq, KAM.Wave.birkFieldW_coord, KAM.Wave.IsBirkHamFieldPlus, KAM.Wave.IsBirkHamFieldPlus.toW, KAM.Wave.IsBirkClassA, KAM.Wave.BirkClassA, KAM.Wave.IsBirkClassA.hamField, KAM.Wave.IsBirkClassA.field_rho (KAM/Wave/Birkhoff/HamClass.lean)
LEAN_NOTE: definition formalized by W3-SETTING; W3-SETTING-DIVF audit 1 FAIL on the general field predicate (F1), audit 2 PASS for the F1 fix (general W-valued IsBirkHamFieldW; former predicate renamed IsBirkHamFieldPlus); class A(U) PASS in audit 1; the remark 'analytic maps are holomorphic' is not restated (Mathlib analytic implies differentiable); X_P o rho = rho o X_P exported for class-A fields (see #hamilton)
NOTE: -

NODE: bpW:w3:real-restrict
KIND: lemma
TITLE: Real restrictions
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:real-restrict@L171-L177
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:real-restrict@L179-L186
CONTRACT_ID: bpW:w3:real-restrict
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; U subset W open with rho U = U; V in {W, W+} with real form E_V in {E_{a,p}, E_{a,p+1}}; f : U -> V analytic with f o rho = rho o f; (second claim) P : U -> C analytic and real
SOURCE_QUANTIFIERS: for all such U, V, f, P
SOURCE_CONCLUSION: f^R(x) = Z^{-1} f(Zx), x in Z^{-1}(U) cap E_{a,p}, takes values in E_V and is real analytic; x -> P(Zx) is real valued and real analytic
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:coords, bpW:w3:ext-series, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:coords | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:real-restrict@L182-L182 | Z and the projection Pi are continuous R-linear
EDGE: bpW:w3:ext-series | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:real-restrict@L180-L180 | C-analytic is R-analytic; compositions
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:real-restrict@L171-L177 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:forms
KIND: definition
TITLE: Smoothing symmetric forms
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:forms@L189-L197
PROOF_SOURCE: -
CONTRACT_ID: bpW:w3:forms
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; d >= 2; P a continuous symmetric d-linear form on W
SOURCE_QUANTIFIERS: P, c
SOURCE_CONCLUSION: defines: P is smoothing with constant c if there is a continuous (d-1)-linear nabla P : W^{d-1} -> W+ with P(w^1,..,w^{d-1},v) = Omega(nabla P(w^1,..),v) and ¦¦nabla P(..)¦¦_+ <= c prod ¦¦w^i¦¦; and records that then X_P(w) = d nabla P(w,..,w), ¦P(w)¦ <= c¦¦w¦¦^d, ¦¦X_P(w)¦¦_+ <= dc¦¦w¦¦^{d-1}, ¦¦X_P(y) - X_P(w)¦¦_+ <= d(d-1)c max(¦¦y¦¦,¦¦w¦¦)^{d-2} ¦¦y - w¦¦
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:omega, bpW:w3:hamfield-def, bpW:w3:ext-multilinear, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:omega | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:forms@L192-L192 | the symplectic form
EDGE: bpW:w3:hamfield-def | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:forms@L194-L194 | the Hamiltonian field X_P
EDGE: bpW:w3:ext-multilinear | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:forms@L194-L194 | derivative of the diagonal of a multilinear map
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:forms@L189-L197 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.IsBirkSmoothing, KAM.Wave.birkDiag, KAM.Wave.birkDiagField, KAM.Wave.birkDiag_field, KAM.Wave.norm_birkDiag_le, KAM.Wave.norm_birkDiagField_le, KAM.Wave.norm_birkDiagField_sub_le, KAM.Wave.birkDiag_analyticOnNhd, KAM.Wave.birkDiagField_analyticOnNhd, KAM.Wave.birkDiag_isClassA (KAM/Wave/Birkhoff/Forms.lean)
LEAN_NOTE: definition formalized by W3-SETTING; W3-SETTING-DIVF audit 1 PASS; birkDiag_field returns the Plus predicate after the F1 fix (audit 2 PASS)
NOTE: -

NODE: bpW:w3:Lambda
KIND: lemma
TITLE: The linear part
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Lambda@L200-L206
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Lambda@L208-L212
CONTRACT_ID: bpW:w3:Lambda
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}
SOURCE_QUANTIFIERS: for all w, v in W; w in W+ for the field; real x
SOURCE_CONCLUSION: Lambda(w) = sum_{j>=1} lambda_j w_j w_{-j} is a continuous quadratic form on W with ¦Lambda(w)¦ <= sqrt(1+m) ¦¦w¦¦^2, Lambda(Zx) = (1/2) sum lambda_j (q_j^2 + p_j^2) for real x; DLambda(w)v = sum_{l != 0} lambda_¦l¦ w_{-l} v_l; for w in W+ its Hamiltonian field is X_Lambda(w)_l = -i lambda'_l w_l, bounded linear W+ -> W of norm <= sqrt(1+m); X_Lambda does not map W into itself
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:space, bpW:w0:H, bpW:w3:coords, bpW:w0:basis#lambda-facts, bpW:w3:hamfield-def, bpW:w1:diag, bpW:w0:basis#lam, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:space | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Lambda@L201-L201 | W, W+ and lambda'
EDGE: bpW:w0:H | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Lambda@L203-L203 | the quadratic part of H
EDGE: bpW:w3:coords | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Lambda@L202-L202 | Z on real points
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Lambda@L209-L209 | lambda_j <= sqrt(1+m) j
EDGE: bpW:w3:hamfield-def | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Lambda@L210-L210 | the field from Definition bpW:w3:hamfield-def
EDGE: bpW:w1:diag | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Lambda@L211-L211 | (i) with r = 1: the operator bound
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Lambda@L201-L201 | lambda occurs directly here (frozen lam)
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Lambda@L200-L206 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: PARTIAL
LEAN_REF: KAM.Wave.birkLamBil, KAM.Wave.birkLambda, KAM.Wave.norm_birkLambda_le, KAM.Wave.birkLambda_analyticOnNhd, KAM.Wave.birkLambda_birkZ, KAM.Wave.fderiv_birkLambda_apply, KAM.Wave.birkXLam, KAM.Wave.norm_birkXLam_le, KAM.Wave.birkLambda_field, KAM.Wave.not_exists_birkXLam_bounded (KAM/Wave/Birkhoff/Lambda.lean)
LEAN_NOTE: W3-SETTING-DIVF audit 1 PASS WITH NOTES (N1), audit 2 PASS (N1 docstring); all clauses proved except 'X_Lambda does not map W into itself', which is exported only as nonexistence of a bounded linear operator on W with the coordinates of X_Lambda (no explicit point of W mapped outside W); no later package closes it
NOTE: -

NODE: bpW:w3:majorant
KIND: lemma
TITLE: Majorant for the cubic sums
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:majorant@L232-L239
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:majorant@L241-L245
CONTRACT_ID: bpW:w3:majorant
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; nonnegative u, u', u'' in l^{a,p}; M(u,u',u'')_l = lambda_l^{-1/2} sum_{i,j,k} ¦g_ijkl¦ u_i u'_j u''_k/sqrt(lambda_i lambda_j lambda_k)
SOURCE_QUANTIFIERS: for all such u, u', u''
SOURCE_CONCLUSION: the sums converge and ¦¦M(u,u',u'')¦¦_{a,p+1} <= C_* ¦¦u¦¦ ¦¦u'¦¦ ¦¦u''¦¦, C_* = K_{p+1/2}^2/pi; C_* does not depend on m; for a = p = 1, C_* = 8(1+2 zeta(3))/pi
CONSTANT_SCOPE: C_* depends only on p (not on m, not on a)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:quartic-coeff, bpW:w0n:algebra, stepW:w0n:majorant, stepW:w0n:selection, stepW:w0n:smoothing, bpW:w0:basis#lam, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:majorant@L234-L234 | the coefficients g_ijkl
EDGE: bpW:w0n:algebra | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:majorant@L237-L237 | K_s
EDGE: stepW:w0n:majorant | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:majorant@L242-L242 | the W0 majorant step applied to q = u
EDGE: stepW:w0n:selection | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:majorant@L242-L242 | the W0 selection step
EDGE: stepW:w0n:smoothing | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:majorant@L242-L242 | the W0 smoothing step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:majorant@L234-L234 | lambda occurs directly here (frozen lam)
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:majorant@L232-L239 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.birkMajorant, KAM.Wave.birkMajorant_eq, KAM.Wave.birkMajorant_bound, KAM.Wave.waveCubicConst_one (KAM/Wave/Birkhoff/Majorant.lean, KAM/Wave/Normal/Analysis/CubicHeadline.lean)
LEAN_NOTE: W3-SETTING-DIVF audit 1 PASS; constant waveCubicConst p = K_{p+1/2}^2/pi independent of m; value 8(1+2 zeta(3))/pi at p = 1 is waveCubicConst_one (W0-ANALYSIS, audit 1 PASS)
NOTE: -

NODE: bpW:w3:quartic
KIND: lemma
TITLE: Quartic forms
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic@L248-L259
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic@L261-L278
CONTRACT_ID: bpW:w3:quartic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; S subset (Z\0)^4 invariant under permutations and x -> -x; c_x with c_x = c_{sigma x} = conj(c_{-x}) and ¦c_x¦ <= ¦frak g_x¦; P(w^1..w^4) = (1/16) sum_{x in S} c_x w^1_{x_1} w^2_{x_2} w^3_{x_3} w^4_{x_4}
SOURCE_QUANTIFIERS: for all such S, c
SOURCE_CONCLUSION: P converges absolutely, is continuous, symmetric, smoothing with constant C_*/4, with nabla P(w^1,w^2,w^3)_l = -(i sgn(l)/16) sum_{y : (y,-l) in S} c_{(y,-l)} w^1_{y_1} w^2_{y_2} w^3_{y_3}; its diagonal P is real; with c = frak g on (Z\0)^4, T, T cap paired, T^c one obtains frak G, frak G^tan, bar frak G, frak G^nor and G, G^tan, bar G, G^nor; G = G^tan + G^nor; ¦¦X_P(w)¦¦_+ <= C_* ¦¦w¦¦^3, ¦P(w)¦ <= (C_*/4)¦¦w¦¦^4 for these P
CONSTANT_SCOPE: C_* depends only on p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:quartic-sec#data, bpW:w3:forms, stepW:w3:maj, stepW:w3:gradbound, stepW:w3:identify, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:quartic-sec#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic@L250-L250 | frak g, pairing and T
EDGE: bpW:w3:forms | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic@L252-L252 | smoothing forms
EDGE: stepW:w3:maj | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic@L262-L262 | proof step
EDGE: stepW:w3:gradbound | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic@L266-L266 | proof step
EDGE: stepW:w3:identify | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic@L270-L270 | proof step
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic@L248-L259 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.IsBirkQuartCoef, KAM.Wave.birkQuartForm, KAM.Wave.birkQuartP, KAM.Wave.birkQuartX, KAM.Wave.birkGradML, KAM.Wave.norm_birkGradML_le, KAM.Wave.birkQuartForm_perm, KAM.Wave.birkQuartForm_rho, KAM.Wave.birkQuart_isSmoothing, KAM.Wave.birkQuart_isClassA, KAM.Wave.norm_birkQuartP_le, KAM.Wave.norm_birkQuartX_le, KAM.Wave.norm_birkQuartX_sub_le, KAM.Wave.isBirkQuartCoef_on, KAM.Wave.birkCoefAll, KAM.Wave.birkCoefTan, KAM.Wave.birkCoefBar, KAM.Wave.birkCoefNor, KAM.Wave.birkCoord_birkGradML, KAM.Wave.birkQuartSum_eq_omega, KAM.Wave.birkQuartP_all_eq_tan_add_nor (KAM/Wave/Birkhoff/QuartForm.lean, KAM/Wave/Birkhoff/QuartMain.lean, KAM/Wave/Birkhoff/QuartML.lean, KAM/Wave/Birkhoff/QuartIdent.lean, KAM/Wave/Birkhoff/QuartBarAlg.lean, KAM/Wave/Birkhoff/QuartPaired.lean, KAM/Wave/Birkhoff/QuartNormal.lean, KAM/Wave/Birkhoff/QuartSum.lean)
LEAN_NOTE: W3-SETTING-DIVF audit 1 PASS (normalization 1/16 and C_*/4 retained)
NOTE: -

NODE: stepW:w3:maj
KIND: step
TITLE: Majorize
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:maj@L262-L265
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:maj@L262-L265
CONTRACT_ID: stepW:w3:maj
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:quartic: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; S subset (Z\0)^4 invariant under permutations and x -> -x; c_x with c_x = c_{sigma x} = conj(c_{-x}) and ¦c_x¦ <= ¦frak g_x¦; P(w^1..w^4) = (1/16) sum_{x in S} c_x w^1_{x_1} w^2_{x_2} w^3_{x_3} w^4_{x_4}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:quartic (for all such S, c); within the step: w^1, w^2, w^3; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: with u^t_i = ¦w^t_i¦ + ¦w^t_{-i}¦, ¦¦u^t¦¦_{a,p} <= sqrt2 ¦¦w^t¦¦ and sum_y ¦frak g_{(y,-l)}¦ ¦w^1_{y_1} w^2_{y_2} w^3_{y_3}¦ <= M(u^1,u^2,u^3)_¦l¦
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:majorant, bpW:w3:quartic-sec#data, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:majorant | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:maj@L265-L265 | the majorant M
EDGE: bpW:w3:quartic-sec#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:maj@L265-L265 | frak g
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:maj@L262-L265 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.birkGrad_majorize, KAM.Wave.birkFoldNorm, KAM.Wave.ellTsumNorm_birkFoldNorm_le (KAM/Wave/Birkhoff/QuartGrad.lean, KAM/Wave/Birkhoff/Fold.lean)
LEAN_NOTE: step of PROVED parent bpW:w3:quartic; W3-SETTING-DIVF audit 1 PASS (quartic majorization ledger rows); (mapping inferred)
NOTE: -

NODE: stepW:w3:gradbound
KIND: step
TITLE: Bound the gradient
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradbound@L266-L269
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradbound@L266-L269
CONTRACT_ID: stepW:w3:gradbound
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:quartic: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; S subset (Z\0)^4 invariant under permutations and x -> -x; c_x with c_x = c_{sigma x} = conj(c_{-x}) and ¦c_x¦ <= ¦frak g_x¦; P(w^1..w^4) = (1/16) sum_{x in S} c_x w^1_{x_1} w^2_{x_2} w^3_{x_3} w^4_{x_4}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:quartic (for all such S, c); within the step: w^1, w^2, w^3; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦¦nabla P¦¦_+ <= (C_*/4) prod ¦¦w^t¦¦
CONSTANT_SCOPE: C_* depends only on p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:majorant, stepW:w3:maj, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:majorant | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradbound@L267-L267 | the bound C_*
EDGE: stepW:w3:maj | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradbound@L268-L268 | the majorization
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradbound@L266-L269 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.norm_birkGradML_le (KAM/Wave/Birkhoff/QuartML.lean)
LEAN_NOTE: step of PROVED parent bpW:w3:quartic; W3-SETTING-DIVF audit 1 PASS
NOTE: -

NODE: stepW:w3:identify
KIND: step
TITLE: Identify
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:identify@L270-L277
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:identify@L270-L277
CONTRACT_ID: stepW:w3:identify
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:quartic: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; S subset (Z\0)^4 invariant under permutations and x -> -x; c_x with c_x = c_{sigma x} = conj(c_{-x}) and ¦c_x¦ <= ¦frak g_x¦; P(w^1..w^4) = (1/16) sum_{x in S} c_x w^1_{x_1} w^2_{x_2} w^3_{x_3} w^4_{x_4}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:quartic (for all such S, c); within the step: w^1, w^2, w^3, v; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Omega(nabla P(w^1,w^2,w^3),v) = P(w^1,w^2,w^3,v); symmetry; reality P(rho w) = conj P(w); the bounds by Definition bpW:w3:forms with d = 4, c = C_*/4; frak g and the four sets are invariant; (Z\0)^4 = T disjoint union T^c
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:omega, stepW:w3:maj, bpW:w3:forms, stepW:w3:gradbound, bpW:w3:coords, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:omega | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:identify@L271-L271 | the form Omega
EDGE: stepW:w3:maj | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:identify@L274-L274 | absolute convergence
EDGE: bpW:w3:forms | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:identify@L276-L276 | the bounds for d = 4
EDGE: stepW:w3:gradbound | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:identify@L276-L276 | c = C_*/4
EDGE: bpW:w3:coords | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:identify@L275-L275 | the involution rho
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:identify@L270-L277 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.birkQuartSum_eq_omega, KAM.Wave.birkQuartForm_perm, KAM.Wave.birkQuartForm_rho, KAM.Wave.isBirkQuartCoef_on (KAM/Wave/Birkhoff/QuartSum.lean, KAM/Wave/Birkhoff/QuartForm.lean, KAM/Wave/Birkhoff/QuartMain.lean)
LEAN_NOTE: step of PROVED parent bpW:w3:quartic; W3-SETTING-DIVF audit 1 PASS
NOTE: -

NODE: bpW:w3:quartic-ident
KIND: lemma
TITLE: Identification with Part~0
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-ident@L282-L291
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-ident@L293-L322
CONTRACT_ID: bpW:w3:quartic-ident
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; real x = (q,p) in E_{a,p}
SOURCE_QUANTIFIERS: for all real x; for all w in W; for x in T
SOURCE_CONCLUSION: G(Zx) = G(q) of Definition bpW:w0:H for a > 0 (definition of G on E_{0,p} for a = 0); Z^{-1} X_G(Zx) = (0,-T(q,q,q)), which is (0,-G_q(q)) for a > 0; G^nor(w) = G^nor(hat w), X_{G^nor} has vanishing tangential components, ¦G^nor(w)¦ <= (C_*/4)¦¦hat w¦¦^4, ¦¦X_{G^nor}(w)¦¦_+ <= C_*¦¦hat w¦¦^3; with I_j := w_j w_{-j}, bar G(w) = (1/2) sum_{i,j in J} A_ij I_i I_j + sum_{j>=3, i in J} B_ji I_i I_j (corrected A, B); x in T with frak g_x != 0 has delta_x = 0 iff x is paired
CONSTANT_SCOPE: C_* depends only on p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:quartic, bpW:w0:H, bpW:w0n:cubic-bound, bpW:w0n:AB, stepW:w3:Gz, stepW:w3:XG, stepW:w3:Gnor, stepW:w3:count, stepW:w3:res, bpW:w0:basis#lam, bpW:w0:Gq#cubicGrad, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-ident@L283-L283 | the forms G, G^nor, bar G
EDGE: bpW:w0:H | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-ident@L283-L283 | G(q) of Definition bpW:w0:H
EDGE: bpW:w0n:cubic-bound | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-ident@L284-L284 | the trilinear T
EDGE: bpW:w0n:AB | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-ident@L289-L289 | the corrected A, B
EDGE: stepW:w3:Gz | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-ident@L294-L294 | proof step
EDGE: stepW:w3:XG | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-ident@L298-L298 | proof step
EDGE: stepW:w3:Gnor | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-ident@L312-L312 | proof step
EDGE: stepW:w3:count | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-ident@L314-L314 | proof step
EDGE: stepW:w3:res | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-ident@L319-L319 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-ident@L315-L315 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-ident@L285-L285 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-ident@L282-L291 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.birkQuartP_birkZ, KAM.Wave.birkQuartP_birkZ_real, KAM.Wave.birkZinv_birkQuartX_birkZ, KAM.Wave.birkQuartP_normal, KAM.Wave.birkQuartX_normal, KAM.Wave.birkQuartX_tangential, KAM.Wave.norm_birkQuartP_normal_le, KAM.Wave.norm_birkQuartX_normal_le, KAM.Wave.birkQuartP_bar, KAM.Wave.birkActionB_eq, KAM.Wave.birkPaired_iff_divisor (KAM/Wave/Birkhoff/QuartIdent.lean, KAM/Wave/Birkhoff/QuartNormal.lean, KAM/Wave/Birkhoff/QuartBarAlg.lean, KAM/Wave/Birkhoff/QuartPaired.lean)
LEAN_NOTE: W3-SETTING-DIVF audit 1 PASS: series identity for a>=0, waveG identity for a>0, X_G = (0,-T(q,q,q)) via landed waveXG, corrected A,B on all complex W, landed quartic_nonresonance applied
NOTE: -

NODE: stepW:w3:Gz
KIND: step
TITLE: The quartic
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Gz@L294-L297
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Gz@L294-L297
CONTRACT_ID: stepW:w3:Gz
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:quartic-ident: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; real x = (q,p) in E_{a,p}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:quartic-ident (for all real x; for all w in W; for x in T); within the step: real x; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: expanding prod(z+zbar) in (bpW:w0n:Gz) gives the two-sided (1/16) sum frak g_x w_x, absolutely convergent by bpW:w3:quartic; for a > 0 it equals the integral-defined G(q) by bpW:w0n:gradient; at a = 0 this series is the definition of G on E_{0,p}, as declared at L283-L284
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:birkhoff#data, bpW:w3:quartic, bpW:w0n:gradient, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:birkhoff#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Gz@L295-L295 | the identity (bpW:w0n:Gz)
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Gz@L296-L296 | absolute convergence
EDGE: bpW:w0n:gradient | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Gz@L297-L297 | G(q) as the quartic sum
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Gz@L294-L297 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w3+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.birkQuartP_birkZ, KAM.Wave.birkQuartP_birkZ_real (KAM/Wave/Birkhoff/QuartIdent.lean)
LEAN_NOTE: step of PROVED parent bpW:w3:quartic-ident; W3-SETTING-DIVF audit 1 PASS
NOTE: -

NODE: stepW:w3:XG
KIND: step
TITLE: The field
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L298-L311
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L298-L311
CONTRACT_ID: stepW:w3:XG
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:quartic-ident: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; real x = (q,p) in E_{a,p}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:quartic-ident (for all real x; for all w in W; for x in T); within the step: real points; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: on real points Z^{-1} X_G = (d_p G, -d_q G) with d_p G = 0; for every a >= 0 (including a = 0), G(Zx) = (1/4) Q(q,q,q,q) with Q(q^1,..,q^4) = sum g_ijkl hat q^1_i hat q^2_j hat q^3_k hat q^4_l absolutely convergent on (l^{a,p})^4 (¦Q¦ <= C_* prod ¦¦q^t¦¦), Q symmetric 4-linear, and d_{q_l} G = Q(q,q,q,e_l) = T(q,q,q)_l; for a > 0 this agrees with the formula of Lemma bpW:w0n:gradient
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:hamfield-def#hamilton, bpW:w0n:cubic-bound, bpW:w3:quartic, stepW:w3:Gz, bpW:w3:majorant, bpW:w0n:quartic-coeff, bpW:w0:basis#lam, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:hamfield-def#hamilton | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L299-L299 | on real points Z^{-1} X_P = (d_p P, -d_q P)
EDGE: bpW:w0n:cubic-bound | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L300-L311 | the trilinear T
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L300-L311 | the a=0 Hamiltonian is the two-sided quartic series defined and bounded here
EDGE: stepW:w3:Gz | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L301-L301 | G(Zx) = (1/4) Q(q,q,q,q) from the quartic step
EDGE: bpW:w3:majorant | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L306-L306 | absolute convergence of Q via the majorant M and C_*
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L307-L307 | symmetry of g gives the symmetry of Q
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L303-L303 | hat q_j = q_j/sqrt(lambda_j) uses the frozen lam definition directly
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L298-L311 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-delta3-W-w3+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.birkZinv_birkQuartX_birkZ, KAM.Wave.waveQuartForm_perm, KAM.Wave.norm_waveQuartForm_le (KAM/Wave/Birkhoff/QuartIdent.lean, KAM/Wave/Cubic/QSymm.lean, KAM/Wave/Cubic/QPair.lean)
LEAN_NOTE: step of PROVED parent bpW:w3:quartic-ident; W3-SETTING-DIVF audit 1 PASS; the symmetric 4-linear Q with its C_* bound is the W1-CUBIC waveQuartForm (W1-CUBIC audit 2 PASS)
NOTE: Writer revision r2 (wave-1 corpus update, inp 99afc128 blueprint cleanup): the step now proves the field formula for every a >= 0 directly; the SOURCE_GAP (a = 0 not covered) is resolved and removed. The citations of bpW:w0n:gradient and bpW:w1:gradient-identity at L310-L311 are consistency remarks for a > 0, not alternative derivations, so the two route nodes are deleted.

NODE: stepW:w3:Gnor
KIND: step
TITLE: Normal part
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Gnor@L312-L313
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Gnor@L312-L313
CONTRACT_ID: stepW:w3:Gnor
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:quartic-ident: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; real x = (q,p) in E_{a,p}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:quartic-ident (for all real x; for all w in W; for x in T); within the step: x in T^c; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: every x in T^c has all ¦x_t¦ >= 3, whence the normal-part claims
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:quartic-sec#data, bpW:w3:quartic, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:quartic-sec#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Gnor@L313-L313 | the set T
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Gnor@L313-L313 | the normal-only size and field bounds use the quartic result at the normal projection
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Gnor@L312-L313 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w3+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.birkQuartP_normal, KAM.Wave.birkQuartX_normal, KAM.Wave.norm_birkQuartP_normal_le, KAM.Wave.norm_birkQuartX_normal_le (KAM/Wave/Birkhoff/QuartNormal.lean)
LEAN_NOTE: step of PROVED parent bpW:w3:quartic-ident; W3-SETTING-DIVF audit 1 PASS
NOTE: -

NODE: stepW:w3:count
KIND: step
TITLE: Count the paired terms
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:count@L314-L318
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:count@L314-L318
CONTRACT_ID: stepW:w3:count
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:quartic-ident: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; real x = (q,p) in E_{a,p}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:quartic-ident (for all real x; for all w in W; for x in T); within the step: 1 <= r <= s, r in J; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the paired terms contribute (3/(2 pi lambda_r lambda_s)) I_r I_s (r < s, 24 orderings) and (1/2) A_rr I_r^2 (r = s, 6 orderings): the coefficients of Theorem bpW:w0n:AB
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:quartic-coeff, bpW:w0n:AB, bpW:w0:basis#lam, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:count@L315-L315 | g_rrss = 1/pi, g_rrrr = 3/(2pi)
EDGE: bpW:w0n:AB | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:count@L318-L318 | A and B
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:count@L315-L315 | lambda occurs directly here (frozen lam)
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:count@L314-L318 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.birkV_sum_eq_six, KAM.Wave.birkV_s0_eq, KAM.Wave.tsum_tan_split, KAM.Wave.birkQuartP_bar (KAM/Wave/Birkhoff/QuartBar.lean, KAM/Wave/Birkhoff/QuartBarAlg.lean)
LEAN_NOTE: step of PROVED parent bpW:w3:quartic-ident, separately named; W3-SETTING-DIVF audit 1 PASS
NOTE: -

NODE: stepW:w3:res
KIND: step
TITLE: Resonance
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:res@L319-L321
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:res@L319-L321
CONTRACT_ID: stepW:w3:res
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:quartic-ident: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; real x = (q,p) in E_{a,p}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:quartic-ident (for all real x; for all w in W; for x in T); within the step: x; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: frak g_x != 0 and delta_x = 0 force pairing
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:nonres, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:nonres | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:res@L320-L320 | applied to the indices ¦x¦ with signs sgn x_t
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:res@L319-L321 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.birkPaired_iff_divisor (KAM/Wave/Birkhoff/QuartPaired.lean)
LEAN_NOTE: step of PROVED parent bpW:w3:quartic-ident, separately named; W3-SETTING-DIVF audit 1 PASS
NOTE: -

NODE: bpW:w3:divisor
KIND: lemma
TITLE: Divisor lower bound; P96-W Lemma~4
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L327-L333
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L335-L374
CONTRACT_ID: bpW:w3:divisor
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; n general in this lemma; x in (Z\0)^4 satisfying the selection rule eps_1¦x_1¦ + .. + eps_4¦x_4¦ = 0 for some eps in {+-1}^4, x not paired; n = min_t ¦x_t¦
SOURCE_QUANTIFIERS: for all such x
SOURCE_CONCLUSION: ¦delta_x¦ >= m/(27 (n^2+m)^{3/2}); consequently, if x in T, frak g_x != 0 and x is not paired, ¦delta_x¦ >= delta_*(m) := m/(27 (4+m)^{3/2})
CONSTANT_SCOPE: delta_* depends only on m
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:quartic-sec#data, bpW:w0:basis#lambda-facts, stepW:w3:sel, stepW:w3:signs, stepW:w3:s0, stepW:w3:s1, stepW:w3:s23, stepW:w3:s1inner, stepW:w3:divconcl, bpW:w0:basis#lam, stepW:w3:divisor#curvature, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:quartic-sec#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L328-L328 | delta_x, pairing, T
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L337-L337 | f'(s) = s/f(s) increasing, f'' = m/f^3 > 0 decreasing
EDGE: stepW:w3:sel | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L339-L339 | proof step
EDGE: stepW:w3:signs | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L343-L343 | proof step
EDGE: stepW:w3:s0 | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L347-L347 | proof step
EDGE: stepW:w3:s1 | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L349-L349 | proof step
EDGE: stepW:w3:s23 | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L354-L354 | proof step
EDGE: stepW:w3:s1inner | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L359-L359 | proof step
EDGE: stepW:w3:divconcl | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L370-L370 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L337-L337 | lambda occurs directly here (frozen lam)
EDGE: stepW:w3:divisor#curvature | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L337-L337 | the curvature or beta comparison from the proof preamble is directly used
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L327-L333 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w3+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.birk_divisor_bound, KAM.Wave.birk_divisor_bound_tan, KAM.Wave.birkDeltaStar, KAM.Wave.birk_divisor_sorted (KAM/Wave/Birkhoff/Divisor.lean)
LEAN_NOTE: W3-DIVISOR-F audit 1 PASS (W3-SETTING-DIVF): exact m/(27(n^2+m)^{3/2}) for all 16 sign patterns, delta_* = m/(27(4+m)^{3/2}); minimum given by an attained index
NOTE: -

NODE: stepW:w3:sel
KIND: step
TITLE: Selection rule
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:sel@L339-L342
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:sel@L339-L342
CONTRACT_ID: stepW:w3:sel
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:divisor: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; n general in this lemma; x in (Z\0)^4 satisfying the selection rule eps_1¦x_1¦ + .. + eps_4¦x_4¦ = 0 for some eps in {+-1}^4, x not paired; n = min_t ¦x_t¦; local data: a <= b <= c <= d the sorted ¦x_1¦..¦x_4¦ (n = a); f(s) = sqrt(s^2+m), lambda_k = f(k); beta = m/(27 lambda_a^3) (proof preamble L336-L338)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:divisor (for all such x); within the step: a <= b <= c <= d sorted ¦x_t¦; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: d = a+b+c or d = b+c-a
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:sel@L339-L342 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.birk_divisor_bound_tan, KAM.Wave.quarticSel_of_quarticCoeff_ne_zero (KAM/Wave/Birkhoff/Divisor.lean, KAM/Wave/Normal/QuarticCoeff.lean)
LEAN_NOTE: step of PROVED parent bpW:w3:divisor; W3-SETTING-DIVF audit 1 PASS; selection rule taken as hypothesis (exists eps) in birk_divisor_bound and derived from the landed selection rule in the tangential corollary
NOTE: -

NODE: stepW:w3:signs
KIND: step
TITLE: Signs
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:signs@L343-L346
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:signs@L343-L346
CONTRACT_ID: stepW:w3:signs
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:divisor: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; n general in this lemma; x in (Z\0)^4 satisfying the selection rule eps_1¦x_1¦ + .. + eps_4¦x_4¦ = 0 for some eps in {+-1}^4, x not paired; n = min_t ¦x_t¦; local data: a <= b <= c <= d the sorted ¦x_1¦..¦x_4¦ (n = a); f(s) = sqrt(s^2+m), lambda_k = f(k); beta = m/(27 lambda_a^3) (proof preamble L336-L338)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:divisor (for all such x); within the step: sign patterns; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: WLOG at most two x_t negative; it suffices to bound the divisor of each sign pattern on (a,b,c,d)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:signs@L343-L346 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.birk_divisor_sorted (KAM/Wave/Birkhoff/Divisor.lean)
LEAN_NOTE: step of PROVED parent bpW:w3:divisor; W3-SETTING-DIVF audit 1 PASS; sorting internal (Tuple.sort), all 16 sign patterns handled
NOTE: -

NODE: stepW:w3:s0
KIND: step
TITLE: No minus sign
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s0@L347-L348
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s0@L347-L348
CONTRACT_ID: stepW:w3:s0
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:divisor: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; n general in this lemma; x in (Z\0)^4 satisfying the selection rule eps_1¦x_1¦ + .. + eps_4¦x_4¦ = 0 for some eps in {+-1}^4, x not paired; n = min_t ¦x_t¦; local data: a <= b <= c <= d the sorted ¦x_1¦..¦x_4¦ (n = a); f(s) = sqrt(s^2+m), lambda_k = f(k); beta = m/(27 lambda_a^3) (proof preamble L336-L338)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:divisor (for all such x); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: with no minus sign delta >= 4 > beta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#lambda-facts, bpW:w0:basis#lam, stepW:w3:divisor#curvature, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s0@L348-L348 | lambda_k > k >= 1
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s0@L348-L348 | lambda occurs directly here (frozen lam)
EDGE: stepW:w3:divisor#curvature | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s0@L348-L348 | the curvature or beta comparison from the proof preamble is directly used
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s0@L347-L348 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w3+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.birkDiv_C0 (KAM/Wave/Birkhoff/DivisorCore.lean)
LEAN_NOTE: step of PROVED parent bpW:w3:divisor, separately named; W3-SETTING-DIVF audit 1 PASS
NOTE: -

NODE: stepW:w3:s1
KIND: step
TITLE: One minus sign
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1@L349-L353
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1@L349-L353
CONTRACT_ID: stepW:w3:s1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:divisor: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; n general in this lemma; x in (Z\0)^4 satisfying the selection rule eps_1¦x_1¦ + .. + eps_4¦x_4¦ = 0 for some eps in {+-1}^4, x not paired; n = min_t ¦x_t¦; local data: a <= b <= c <= d the sorted ¦x_1¦..¦x_4¦ (n = a); f(s) = sqrt(s^2+m), lambda_k = f(k); beta = m/(27 lambda_a^3) (proof preamble L336-L338)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:divisor (for all such x); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: with one minus sign the divisor is >= m/(2 lambda_a) >= beta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w3:sel, bpW:w0:basis#lambda-facts, bpW:w0:basis#lam, stepW:w3:divisor#curvature, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w3:sel | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1@L353-L353 | a + b + c >= d
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1@L350-L350 | f(k) - k = m/(f(k)+k); lambda_c + c <= lambda_d + d
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1@L350-L350 | lambda occurs directly here (frozen lam)
EDGE: stepW:w3:divisor#curvature | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1@L352-L352 | the curvature or beta comparison from the proof preamble is directly used
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1@L349-L353 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w3+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.birkDiv_C1 (KAM/Wave/Birkhoff/DivisorCore.lean)
LEAN_NOTE: step of PROVED parent bpW:w3:divisor, separately named; W3-SETTING-DIVF audit 1 PASS
NOTE: -

NODE: stepW:w3:s23
KIND: step
TITLE: Two minus signs, outer pairs
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s23@L354-L358
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s23@L354-L358
CONTRACT_ID: stepW:w3:s23
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:divisor: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; n general in this lemma; x in (Z\0)^4 satisfying the selection rule eps_1¦x_1¦ + .. + eps_4¦x_4¦ = 0 for some eps in {+-1}^4, x not paired; n = min_t ¦x_t¦; local data: a <= b <= c <= d the sorted ¦x_1¦..¦x_4¦ (n = a); f(s) = sqrt(s^2+m), lambda_k = f(k); beta = m/(27 lambda_a^3) (proof preamble L336-L338)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:divisor (for all such x); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: delta_3 = lambda_c + lambda_d - lambda_a - lambda_b and delta_2 = (lambda_b - lambda_a) + (lambda_d - lambda_c) vanish identically iff paired, and otherwise are >= a/lambda_a >= beta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#lambda-facts, bpW:w0:basis#lam, stepW:w3:divisor#curvature, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s23@L356-L356 | lambda_{k+1} - lambda_k >= f'(k) >= f'(a)
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s23@L355-L355 | lambda occurs directly here (frozen lam)
EDGE: stepW:w3:divisor#curvature | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s23@L357-L357 | the curvature or beta comparison from the proof preamble is directly used
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s23@L354-L358 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w3+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.birkDiv_C3, KAM.Wave.birkDiv_C2, KAM.Wave.birkDelta_ge (KAM/Wave/Birkhoff/DivisorCore.lean, KAM/Wave/Birkhoff/DivisorReal.lean)
LEAN_NOTE: step of PROVED parent bpW:w3:divisor, separately named; W3-SETTING-DIVF audit 1 PASS
NOTE: -

NODE: stepW:w3:s1inner
KIND: step
TITLE: Two minus signs, inner pair
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1inner@L359-L369
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1inner@L359-L369
CONTRACT_ID: stepW:w3:s1inner
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:divisor: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; n general in this lemma; x in (Z\0)^4 satisfying the selection rule eps_1¦x_1¦ + .. + eps_4¦x_4¦ = 0 for some eps in {+-1}^4, x not paired; n = min_t ¦x_t¦; local data: a <= b <= c <= d the sorted ¦x_1¦..¦x_4¦ (n = a); f(s) = sqrt(s^2+m), lambda_k = f(k); beta = m/(27 lambda_a^3) (proof preamble L336-L338)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:divisor (for all such x); within the step: cases (i), (ii); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: delta_1 = lambda_a + lambda_d - lambda_b - lambda_c is paired iff a = b, c = d, and otherwise >= beta: (i) d = b+c-a via f'' >= m/(27 lambda_a^3); (ii) d = a+b+c via 2a f'(b) >= 2/sqrt(1+m) >= beta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w3:sel, bpW:w0:basis#lambda-facts, bpW:w0:basis#lam, bpW:w3:ext-integral, stepW:w3:divisor#curvature, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w3:sel | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1inner@L362-L362 | the two cases d = b+c-a, d = a+b+c
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1inner@L363-L363 | f' increasing, f'' = m/f^3
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1inner@L360-L360 | lambda occurs directly here (frozen lam)
EDGE: bpW:w3:ext-integral | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1inner@L363-L363 | the double integral argument uses the fundamental theorem of calculus
EDGE: stepW:w3:divisor#curvature | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1inner@L364-L364 | the curvature or beta comparison from the proof preamble is directly used
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1inner@L359-L369 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w3+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.birkDiv_C1i, KAM.Wave.birkDiv_C1ii, KAM.Wave.birkL_second_diff (KAM/Wave/Birkhoff/DivisorCore.lean, KAM/Wave/Birkhoff/DivisorReal.lean)
LEAN_NOTE: step of PROVED parent bpW:w3:divisor, separately named; W3-SETTING-DIVF audit 1 PASS; route deviation: f'' integral replaced by the exact algebraic second-difference bound (same constants); Lean route differs: discrete second differences replace the derivative facts
NOTE: -

NODE: stepW:w3:divconcl
KIND: step
TITLE: Conclusion
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:divconcl@L370-L373
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:divconcl@L370-L373
CONTRACT_ID: stepW:w3:divconcl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:divisor: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; n general in this lemma; x in (Z\0)^4 satisfying the selection rule eps_1¦x_1¦ + .. + eps_4¦x_4¦ = 0 for some eps in {+-1}^4, x not paired; n = min_t ¦x_t¦; local data: a <= b <= c <= d the sorted ¦x_1¦..¦x_4¦ (n = a); f(s) = sqrt(s^2+m), lambda_k = f(k); beta = m/(27 lambda_a^3) (proof preamble L336-L338)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:divisor (for all such x); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: two-minus patterns are +-delta_1, +-delta_2, +-delta_3 and pairing coincides with identical vanishing; the corollary follows since frak g_x != 0 implies the selection rule, n <= 2 on T, and n -> m/(n^2+m)^{3/2} is decreasing
CONSTANT_SCOPE: delta_* depends only on m
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w3:s0, stepW:w3:s1, stepW:w3:s23, stepW:w3:s1inner, bpW:w0n:quartic-coeff, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w3:s0 | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:divconcl@L371-L371 | no minus sign
EDGE: stepW:w3:s1 | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:divconcl@L371-L371 | one minus sign
EDGE: stepW:w3:s23 | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:divconcl@L371-L371 | delta_2, delta_3
EDGE: stepW:w3:s1inner | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:divconcl@L371-L371 | delta_1
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:divconcl@L373-L373 | frak g_x != 0 implies the selection rule
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:divconcl@L370-L373 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.birk_divisor_sorted, KAM.Wave.birk_divisor_bound, KAM.Wave.birk_divisor_bound_tan, KAM.Wave.birkDeltaStar (KAM/Wave/Birkhoff/Divisor.lean)
LEAN_NOTE: step of PROVED parent bpW:w3:divisor; W3-SETTING-DIVF audit 1 PASS
NOTE: -

NODE: bpW:w3:Fdef
KIND: definition
TITLE: Generating Hamiltonian
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Fdef@L395-L401
PROOF_SOURCE: -
CONTRACT_ID: bpW:w3:Fdef
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}
SOURCE_QUANTIFIERS: x; w^1..w^4
SOURCE_CONCLUSION: defines f_x = frak g_x/delta_x for x in T not paired, f_x = 0 otherwise (Lean: division by 0 is 0; Lemma bpW:w3:divisor guarantees delta_x != 0 where frak g_x != 0); frak F(w^1..w^4) = (i/16) sum_x f_x w^1_{x_1} .. w^4_{x_4}, F(w) = frak F(w,w,w,w), S = 4 nabla frak F : W^3 -> W+, X_F(w) = S(w,w,w)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:quartic-sec#data, bpW:w3:forms, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:quartic-sec#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Fdef@L396-L396 | frak g, delta, pairing, T
EDGE: bpW:w3:forms | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Fdef@L400-L400 | nabla of a form
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Fdef@L395-L401 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.birkFx, KAM.Wave.birkFcoef, KAM.Wave.birkFform, KAM.Wave.birkFgrad, KAM.Wave.birkS, KAM.Wave.birkXF_eq (KAM/Wave/Birkhoff/FCoef.lean, KAM/Wave/Birkhoff/FForm.lean)
LEAN_NOTE: definition formalized by W3-DIVISOR-F; W3-SETTING-DIVF audit 1 PASS (Fdef row)
NOTE: -

NODE: bpW:w3:F
KIND: theorem
TITLE: $F$ is bounded and one-smoothing
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:F@L406-L413
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:F@L415-L424
CONTRACT_ID: bpW:w3:F
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; frak F, F, S of Definition bpW:w3:Fdef
SOURCE_QUANTIFIERS: for all w, w^i, v
SOURCE_CONCLUSION: frak F is a continuous symmetric 4-linear form, smoothing with constant C_*/(4 delta_*), F real; S is a continuous symmetric trilinear W^3 -> W+ with ¦¦S(w^1,w^2,w^3)¦¦_+ <= C_F prod ¦¦w^i¦¦, C_F = C_*/delta_*(m) = 27 C_* (4+m)^{3/2}/m; Omega(S(w^1,w^2,w^3),v) = 4 frak F(w^1,w^2,w^3,v) symmetric in all four; S commutes with rho; ¦F(w)¦ <= (C_F/4)¦¦w¦¦^4; X_F is a cubic polynomial, analytic W -> W+
CONSTANT_SCOPE: C_F depends on m and p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:Fdef, stepW:w3:fcoef, stepW:w3:Fconcl, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:Fdef | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:F@L407-L407 | frak F, F, S
EDGE: stepW:w3:fcoef | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:F@L416-L416 | proof step
EDGE: stepW:w3:Fconcl | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:F@L420-L420 | proof step
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:F@L406-L413 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.birkF_isSmoothing, KAM.Wave.birkCF, KAM.Wave.norm_birkS_le, KAM.Wave.birkS_pairing, KAM.Wave.birkS_perm, KAM.Wave.birkS_rho, KAM.Wave.birkF_real, KAM.Wave.norm_birkF_le, KAM.Wave.birkXF_eq, KAM.Wave.birkF_isClassA (KAM/Wave/Birkhoff/FForm.lean)
LEAN_NOTE: W3-SETTING-DIVF audit 1 PASS: S into W+ with C_F = C_*/delta_*, four-slot pairing symmetry, reality, X_F analytic W to W+
NOTE: -

NODE: stepW:w3:fcoef
KIND: step
TITLE: Coefficients
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:fcoef@L416-L419
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:fcoef@L416-L419
CONTRACT_ID: stepW:w3:fcoef
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:F: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; frak F, F, S of Definition bpW:w3:Fdef
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:F (for all w, w^i, v); within the step: x; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: f is permutation invariant, f_{-x} = -f_x, ¦f_x¦ <= ¦frak g_x¦/delta_*; c_x := i delta_* f_x satisfies the hypotheses of Lemma bpW:w3:quartic and frak F = delta_*^{-1} P_c
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:divisor, bpW:w3:quartic, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:divisor | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:fcoef@L418-L418 | ¦delta_x¦ >= delta_*
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:fcoef@L418-L418 | its coefficient hypotheses
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:fcoef@L416-L419 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.birkFx_perm, KAM.Wave.birkFx_neg, KAM.Wave.abs_birkFx_le, KAM.Wave.birkFcoef_isCoef, KAM.Wave.birkFform (KAM/Wave/Birkhoff/FCoef.lean, KAM/Wave/Birkhoff/FForm.lean)
LEAN_NOTE: step of PROVED parent bpW:w3:F, separately named; W3-SETTING-DIVF audit 1 PASS
NOTE: -

NODE: stepW:w3:Fconcl
KIND: step
TITLE: Conclusions
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Fconcl@L420-L423
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Fconcl@L420-L423
CONTRACT_ID: stepW:w3:Fconcl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:F: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; frak F, F, S of Definition bpW:w3:Fdef
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:F (for all w, w^i, v); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: smoothing with constant C_*/(4 delta_*) and reality; S = 4 nabla frak F gives C_F; reality of S; analyticity of X_F
CONSTANT_SCOPE: C_F depends on m and p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:quartic, stepW:w3:fcoef, bpW:w3:hamfield-def, bpW:w3:ext-series, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Fconcl@L421-L421 | smoothing and reality of P_c
EDGE: stepW:w3:fcoef | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Fconcl@L421-L421 | frak F = P_c/delta_*
EDGE: bpW:w3:hamfield-def | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Fconcl@L423-L423 | reality of the field from reality of the form
EDGE: bpW:w3:ext-series | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Fconcl@L423-L423 | polynomials are analytic
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Fconcl@L420-L423 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.birkF_isSmoothing, KAM.Wave.norm_birkS_le, KAM.Wave.birkS_rho, KAM.Wave.birkF_isClassA (KAM/Wave/Birkhoff/FForm.lean)
LEAN_NOTE: step of PROVED parent bpW:w3:F; W3-SETTING-DIVF audit 1 PASS
NOTE: -

NODE: bpW:w3:homological
KIND: proposition
TITLE: Homological identity
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:homological@L427-L432
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:homological@L434-L449
CONTRACT_ID: bpW:w3:homological
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Z' = bar G - G^tan, the diagonal of frak z = bar frak G - frak G^tan
SOURCE_QUANTIFIERS: for every w in W
SOURCE_CONCLUSION: frak z is a form as in Lemma bpW:w3:quartic, smoothing with constant C_*/4, ¦¦X_{Z'}(w)¦¦_+ <= C_*¦¦w¦¦^3; DLambda(w) X_F(w) = Z'(w), equivalently G + DLambda . X_F = bar G + G^nor
CONSTANT_SCOPE: C_* depends only on p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:quartic, stepW:w3:Xfcoord, stepW:w3:euler, stepW:w3:divide, bpW:w0:basis#lam, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:homological@L428-L428 | the forms bar frak G, frak G^tan and their bounds
EDGE: stepW:w3:Xfcoord | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:homological@L435-L435 | proof step
EDGE: stepW:w3:euler | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:homological@L438-L438 | proof step
EDGE: stepW:w3:divide | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:homological@L444-L444 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:homological@L439-L439 | lambda occurs directly here (frozen lam)
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:homological@L427-L432 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.birk_homological, KAM.Wave.birk_homological', KAM.Wave.birk_DLam_XF, KAM.Wave.birk_euler, KAM.Wave.birk_delta_mul_fx, KAM.Wave.summable_birkLamQuartTerm (KAM/Wave/Birkhoff/Homological.lean, KAM/Wave/Birkhoff/HomSum.lean)
LEAN_NOTE: W3-SETTING-DIVF audit 1 PASS: DLambda(w) X_F(w) = bar G(w) - G^tan(w) for every w in W, and G + DLambda X_F = bar G + G^nor; the parenthetical class of the form frak z (smoothing C_*/4, bound on X_Z') has no separately named export
NOTE: -

NODE: stepW:w3:Xfcoord
KIND: step
TITLE: Field coordinates
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Xfcoord@L435-L437
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Xfcoord@L435-L437
CONTRACT_ID: stepW:w3:Xfcoord
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:homological: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Z' = bar G - G^tan, the diagonal of frak z = bar frak G - frak G^tan
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:homological (for every w in W); within the step: w, l; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: X_F(w)_l = 4 nabla frak F(w,w,w)_l = (sgn(l)/4) sum_y f_{(y,-l)} w_y
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:Fdef, bpW:w3:quartic, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:Fdef | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Xfcoord@L436-L436 | S = 4 nabla frak F
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Xfcoord@L436-L436 | the formula for nabla
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Xfcoord@L435-L437 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.birkCoord_birkXF, KAM.Wave.birkXF_eq (KAM/Wave/Birkhoff/Homological.lean, KAM/Wave/Birkhoff/FForm.lean)
LEAN_NOTE: step of PROVED parent bpW:w3:homological; W3-SETTING-DIVF audit 1 PASS
NOTE: -

NODE: stepW:w3:euler
KIND: step
TITLE: Euler identity
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:euler@L438-L443
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:euler@L438-L443
CONTRACT_ID: stepW:w3:euler
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:homological: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Z' = bar G - G^tan, the diagonal of frak z = bar frak G - frak G^tan
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:homological (for every w in W); within the step: w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: DLambda(w) X_F(w) = -(1/16) sum_x delta_x f_x w_x, all series absolutely convergent
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:Lambda, stepW:w3:Xfcoord, bpW:w3:F, bpW:w0:basis#lambda-facts, bpW:w0:basis#lam, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:Lambda | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:euler@L439-L439 | DLambda(w)v
EDGE: stepW:w3:Xfcoord | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:euler@L439-L439 | the coordinates of X_F
EDGE: bpW:w3:F | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:euler@L443-L443 | ¦¦X_F(w)¦¦_+ < infinity
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:euler@L442-L442 | lambda_¦l¦ <= sqrt(1+m) ¦l¦^{p+1} e^{a¦l¦}
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:euler@L439-L439 | lambda occurs directly here (frozen lam)
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:euler@L438-L443 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.birk_euler, KAM.Wave.birk_DLam_XF, KAM.Wave.summable_birkLamQuartTerm (KAM/Wave/Birkhoff/Homological.lean, KAM/Wave/Birkhoff/HomSum.lean)
LEAN_NOTE: step of PROVED parent bpW:w3:homological, separately named; W3-SETTING-DIVF audit 1 PASS
NOTE: -

NODE: stepW:w3:divide
KIND: step
TITLE: Divide
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:divide@L444-L448
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:divide@L444-L448
CONTRACT_ID: stepW:w3:divide
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:homological: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Z' = bar G - G^tan, the diagonal of frak z = bar frak G - frak G^tan
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:homological (for every w in W); within the step: w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: delta_x f_x = frak g_x on T \ paired and 0 else, so the sum is bar G - G^tan; with G = G^tan + G^nor the second form
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w3:euler, bpW:w3:divisor, bpW:w3:quartic, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w3:euler | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:divide@L446-L446 | the sum
EDGE: bpW:w3:divisor | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:divide@L446-L446 | delta_x != 0 where frak g_x != 0
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:divide@L447-L447 | the forms and G = G^tan + G^nor
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:divide@L444-L448 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.birk_delta_mul_fx, KAM.Wave.birk_homological, KAM.Wave.birk_homological' (KAM/Wave/Birkhoff/Homological.lean)
LEAN_NOTE: step of PROVED parent bpW:w3:homological; W3-SETTING-DIVF audit 1 PASS
NOTE: -

NODE: bpW:w3:lie-coeff
KIND: definition
TITLE: Lie coefficients
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:lie-coeff@L461-L466
PROOF_SOURCE: -
CONTRACT_ID: bpW:w3:lie-coeff
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; S of Definition bpW:w3:Fdef
SOURCE_QUANTIFIERS: k >= 0
SOURCE_CONCLUSION: defines the continuous (2k+1)-linear Phi_k : W^{2k+1} -> W by Phi_0(w) = w and the recursion Phi_{k+1}(w^1..w^{2k+3}) = (1/(k+1)) sum_{i=1}^{2k+1} Phi_k(w^1,..,w^{i-1},S(w^i,w^{i+1},w^{i+2}),w^{i+3},..), phi_k(w) = Phi_k(w,..,w), and (LQ)(w) = DQ(w) X_F(w) for C^1 maps Q
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:Fdef, bpW:w3:F, bpW:w3:ext-multilinear, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:Fdef | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:lie-coeff@L463-L463 | S and X_F
EDGE: bpW:w3:F | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:lie-coeff@L463-L463 | S must be a continuous trilinear map to construct continuous Lie coefficients
EDGE: bpW:w3:ext-multilinear | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:lie-coeff@L463-L463 | slot insertion preserves continuous multilinearity
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:lie-coeff@L461-L466 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w3+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:leibniz
KIND: lemma
TITLE: Coefficient bounds and the Leibniz identity
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:leibniz@L470-L480
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:leibniz@L482-L501
CONTRACT_ID: bpW:w3:leibniz
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Phi_k, phi_k, L of Definition bpW:w3:lie-coeff
SOURCE_QUANTIFIERS: for all k >= 0
SOURCE_CONCLUSION: (i) phi_{k+1} = L phi_k/(k+1), phi_k = L^k(id)/k!; (ii) ¦¦Phi_k¦¦ <= (2C_F)^k and for k >= 1 Phi_k takes values in W+ with ¦¦Phi_k¦¦_{W^{2k+1} -> W+} <= (2C_F)^k; (iii) Phi_k commutes with rho; (iv) (k+1) phi_{k+1} = sum_{a+b+c=k} S(phi_a,phi_b,phi_c) and (k+1) D phi_{k+1}(w)v = sum_{a+b+c=k} 3 S(D phi_a(w)v, phi_b(w), phi_c(w))
CONSTANT_SCOPE: C_F depends on m and p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:lie-coeff, stepW:w3:rec, stepW:w3:norms, stepW:w3:Phireal, stepW:w3:leib, stepW:w3:leibid, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:lie-coeff | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:leibniz@L473-L473 | Phi_k, phi_k, L
EDGE: stepW:w3:rec | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:leibniz@L483-L483 | proof step
EDGE: stepW:w3:norms | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:leibniz@L486-L486 | proof step
EDGE: stepW:w3:Phireal | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:leibniz@L491-L491 | proof step
EDGE: stepW:w3:leib | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:leibniz@L493-L493 | proof step
EDGE: stepW:w3:leibid | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:leibniz@L497-L497 | proof step
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:leibniz@L470-L480 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:rec
KIND: step
TITLE: Recursion
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:rec@L483-L485
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:rec@L483-L485
CONTRACT_ID: stepW:w3:rec
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:leibniz: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Phi_k, phi_k, L of Definition bpW:w3:lie-coeff
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:leibniz (for all k >= 0); within the step: k; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (i): D phi_k(w)v = sum_i Phi_k(w,..,v,..,w) with v = S(w,w,w)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:ext-multilinear, bpW:w3:lie-coeff, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:ext-multilinear | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:rec@L484-L484 | derivative of the diagonal
EDGE: bpW:w3:lie-coeff | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:rec@L485-L485 | the recursion
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:rec@L483-L485 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:norms
KIND: step
TITLE: Norms
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:norms@L486-L490
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:norms@L486-L490
CONTRACT_ID: stepW:w3:norms
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:leibniz: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Phi_k, phi_k, L of Definition bpW:w3:lie-coeff
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:leibniz (for all k >= 0); within the step: k; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (ii): ¦¦Phi_{k+1}¦¦ <= 2 C_F ¦¦Phi_k¦¦ in W and in W+
CONSTANT_SCOPE: C_F depends on m and p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:ext-multilinear, bpW:w3:F, bpW:w3:lie-coeff, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:ext-multilinear | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:norms@L487-L487 | norms of inserted multilinear maps
EDGE: bpW:w3:F | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:norms@L487-L487 | ¦¦S¦¦ <= C_F
EDGE: bpW:w3:lie-coeff | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:norms@L489-L489 | Phi_1 = S and the recursion
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:norms@L486-L490 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:Phireal
KIND: step
TITLE: Reality
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Phireal@L491-L492
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Phireal@L491-L492
CONTRACT_ID: stepW:w3:Phireal
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:leibniz: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Phi_k, phi_k, L of Definition bpW:w3:lie-coeff
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:leibniz (for all k >= 0); within the step: k; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iii) by induction
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:F, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:F | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Phireal@L492-L492 | S commutes with rho
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Phireal@L491-L492 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:leib
KIND: step
TITLE: Leibniz rule
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:leib@L493-L496
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:leib@L493-L496
CONTRACT_ID: stepW:w3:leib
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:leibniz: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Phi_k, phi_k, L of Definition bpW:w3:lie-coeff
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:leibniz (for all k >= 0); within the step: n; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: for continuous multilinear B and C^infinity Q_i, L B(Q_1..Q_r) = sum_i B(..,LQ_i,..) and the multinomial formula for L^n B(Q_1..Q_r)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:ext-multilinear, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:ext-multilinear | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:leib@L494-L494 | product and chain rules for multilinear maps
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:leib@L493-L496 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:leibid
KIND: step
TITLE: The identity
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:leibid@L497-L500
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:leibid@L497-L500
CONTRACT_ID: stepW:w3:leibid
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:leibniz: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Phi_k, phi_k, L of Definition bpW:w3:lie-coeff
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:leibniz (for all k >= 0); within the step: k; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iv): (k+1)! phi_{k+1} = L^k(S(id,id,id)) = sum_{a+b+c=k} (k!/(a!b!c!)) S(a! phi_a, b! phi_b, c! phi_c), and the derivative identity by symmetry of S
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w3:rec, stepW:w3:leib, bpW:w3:F, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w3:rec | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:leibid@L499-L499 | (i)
EDGE: stepW:w3:leib | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:leibid@L499-L499 | the Leibniz rule
EDGE: bpW:w3:F | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:leibid@L500-L500 | symmetry of S
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:leibid@L497-L500 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:flow
KIND: theorem
TITLE: The flow of $X_F$
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L504-L527
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L529-L566
CONTRACT_ID: bpW:w3:flow
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; rho_0 = rho_0(m) = (40 C_F)^{-1/2}, B_rho = {w : ¦¦w¦¦ < rho}; Gamma_t(w) = sum_k t^k phi_k(w) for real ¦t¦ < 2, w in B_{rho_0}; r = 2¦t¦ C_F ¦¦w¦¦^2; (vi) rho_1 = rho_0/2
SOURCE_QUANTIFIERS: for real ¦t¦ < 2 and w in B_{rho_0} ((vi): ¦t¦ <= 1, w in B_{rho_1})
SOURCE_CONCLUSION: r <= 1/10; (i) the series converges absolutely, w -> Gamma_t(w) has the power series (t^k Phi_k) on B_{rho_0} and is analytic, Gamma_t - id is analytic B_{rho_0} -> W+, (t,w) -> Gamma_t(w) is C^1; (ii) Gamma_0 = id, d_t Gamma_t = X_F(Gamma_t) and d_t Gamma_t = D Gamma_t X_F; (iii) ¦¦Gamma_t(w)¦¦ <= (10/9)¦¦w¦¦, ¦¦Gamma_t(w) - w¦¦_+ <= 3¦t¦C_F¦¦w¦¦^3, ¦¦D Gamma_t(w) - I¦¦_{W -> W+} <= 10¦t¦C_F¦¦w¦¦^2 <= 1/2, D Gamma_t(w) maps W+ into itself, is invertible on W and W+ with inverses of norm <= 2 and ¦¦D Gamma_t^{-1} - I¦¦_{W -> W+} <= 20¦t¦C_F¦¦w¦¦^2; (iv) Gamma_t(rho w) = rho Gamma_t(w); (v) d_t D Gamma_t(w)v = DX_F(Gamma_t(w)) D Gamma_t(w)v, DX_F(y)xi = 3S(y,y,xi); (vi) Gamma_{-t}(Gamma_t(w)) = w, Gamma = Gamma_1 is injective on B_{rho_1}, Gamma(B_{rho_1}) subset B_{10 rho_1/9} and Gamma(B_{rho_1}) contains B_{9 rho_1/10}
CONSTANT_SCOPE: rho_0, rho_1 depend on m and p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:lie-coeff, bpW:w3:F, stepW:w3:conv, stepW:w3:floweq, stepW:w3:transport, stepW:w3:est, stepW:w3:Greal, stepW:w3:var, stepW:w3:inv, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:lie-coeff | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L507-L507 | phi_k
EDGE: bpW:w3:F | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L505-L505 | C_F
EDGE: stepW:w3:conv | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L530-L530 | proof step
EDGE: stepW:w3:floweq | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L538-L538 | proof step
EDGE: stepW:w3:transport | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L542-L542 | proof step
EDGE: stepW:w3:est | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L545-L545 | proof step
EDGE: stepW:w3:Greal | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L552-L552 | proof step
EDGE: stepW:w3:var | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L554-L554 | proof step
EDGE: stepW:w3:inv | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L558-L558 | proof step
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L504-L527 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w3+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:conv
KIND: step
TITLE: Convergence and analyticity
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conv@L530-L537
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conv@L530-L537
CONTRACT_ID: stepW:w3:conv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:flow: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; rho_0 = rho_0(m) = (40 C_F)^{-1/2}, B_rho = {w : ¦¦w¦¦ < rho}; Gamma_t(w) = sum_k t^k phi_k(w) for real ¦t¦ < 2, w in B_{rho_0}; r = 2¦t¦ C_F ¦¦w¦¦^2; (vi) rho_1 = rho_0/2
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:flow (for real ¦t¦ < 2 and w in B_{rho_0} ((vi): ¦t¦ <= 1, w in B_{rho_1})); within the step: t, w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦t¦^k ¦¦phi_k(w)¦¦ <= r^k ¦¦w¦¦, r <= 1/10; the formal series with coefficients t^k Phi_k gives analyticity in W and (k >= 1) in W+; termwise derivatives in (t,w) are summable, giving joint C^1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:leibniz, bpW:w3:ext-series, bpW:w3:ext-tsum, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:leibniz | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conv@L531-L531 | (ii) the coefficient bounds
EDGE: bpW:w3:ext-series | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conv@L534-L534 | power series give analyticity
EDGE: bpW:w3:ext-tsum | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conv@L537-L537 | termwise differentiation
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conv@L530-L537 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w3+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:floweq
KIND: step
TITLE: Flow equation
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:floweq@L538-L541
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:floweq@L538-L541
CONTRACT_ID: stepW:w3:floweq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:flow: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; rho_0 = rho_0(m) = (40 C_F)^{-1/2}, B_rho = {w : ¦¦w¦¦ < rho}; Gamma_t(w) = sum_k t^k phi_k(w) for real ¦t¦ < 2, w in B_{rho_0}; r = 2¦t¦ C_F ¦¦w¦¦^2; (vi) rho_1 = rho_0/2
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:flow (for real ¦t¦ < 2 and w in B_{rho_0} ((vi): ¦t¦ <= 1, w in B_{rho_1})); within the step: t, w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: d_t Gamma_t = S(Gamma_t,Gamma_t,Gamma_t) = X_F(Gamma_t)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:leibniz, bpW:w3:ext-tsum, stepW:w3:conv, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:leibniz | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:floweq@L540-L540 | (iv)
EDGE: bpW:w3:ext-tsum | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:floweq@L541-L541 | Cauchy product
EDGE: stepW:w3:conv | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:floweq@L539-L539 | termwise derivative
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:floweq@L538-L541 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w3+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:transport
KIND: step
TITLE: Transport equation
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:transport@L542-L544
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:transport@L542-L544
CONTRACT_ID: stepW:w3:transport
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:flow: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; rho_0 = rho_0(m) = (40 C_F)^{-1/2}, B_rho = {w : ¦¦w¦¦ < rho}; Gamma_t(w) = sum_k t^k phi_k(w) for real ¦t¦ < 2, w in B_{rho_0}; r = 2¦t¦ C_F ¦¦w¦¦^2; (vi) rho_1 = rho_0/2
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:flow (for real ¦t¦ < 2 and w in B_{rho_0} ((vi): ¦t¦ <= 1, w in B_{rho_1})); within the step: t, w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: d_t Gamma_t = D Gamma_t X_F
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:leibniz, stepW:w3:conv, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:leibniz | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:transport@L544-L544 | (i)
EDGE: stepW:w3:conv | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:transport@L544-L544 | termwise derivatives
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:transport@L542-L544 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w3+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:est
KIND: step
TITLE: Estimates
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:est@L545-L551
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:est@L545-L551
CONTRACT_ID: stepW:w3:est
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:flow: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; rho_0 = rho_0(m) = (40 C_F)^{-1/2}, B_rho = {w : ¦¦w¦¦ < rho}; Gamma_t(w) = sum_k t^k phi_k(w) for real ¦t¦ < 2, w in B_{rho_0}; r = 2¦t¦ C_F ¦¦w¦¦^2; (vi) rho_1 = rho_0/2
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:flow (for real ¦t¦ < 2 and w in B_{rho_0} ((vi): ¦t¦ <= 1, w in B_{rho_1})); within the step: t, w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the bounds of (iii) and the inverses
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:leibniz, bpW:w3:ext-neumann, stepW:w3:conv, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:leibniz | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:est@L547-L547 | (ii)
EDGE: bpW:w3:ext-neumann | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:est@L550-L550 | Neumann series
EDGE: stepW:w3:conv | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:est@L546-L546 | r <= 1/10
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:est@L545-L551 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w3+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:Greal
KIND: step
TITLE: Reality
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Greal@L552-L553
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Greal@L552-L553
CONTRACT_ID: stepW:w3:Greal
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:flow: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; rho_0 = rho_0(m) = (40 C_F)^{-1/2}, B_rho = {w : ¦¦w¦¦ < rho}; Gamma_t(w) = sum_k t^k phi_k(w) for real ¦t¦ < 2, w in B_{rho_0}; r = 2¦t¦ C_F ¦¦w¦¦^2; (vi) rho_1 = rho_0/2
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:flow (for real ¦t¦ < 2 and w in B_{rho_0} ((vi): ¦t¦ <= 1, w in B_{rho_1})); within the step: t real; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iv) termwise
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:leibniz, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:leibniz | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Greal@L553-L553 | (iii)
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Greal@L552-L553 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w3+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:var
KIND: step
TITLE: Variational equation
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:var@L554-L557
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:var@L554-L557
CONTRACT_ID: stepW:w3:var
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:flow: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; rho_0 = rho_0(m) = (40 C_F)^{-1/2}, B_rho = {w : ¦¦w¦¦ < rho}; Gamma_t(w) = sum_k t^k phi_k(w) for real ¦t¦ < 2, w in B_{rho_0}; r = 2¦t¦ C_F ¦¦w¦¦^2; (vi) rho_1 = rho_0/2
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:flow (for real ¦t¦ < 2 and w in B_{rho_0} ((vi): ¦t¦ <= 1, w in B_{rho_1})); within the step: t, w, v; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: d_t D Gamma_t v = 3S(D Gamma_t v, Gamma_t, Gamma_t)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:leibniz, bpW:w3:ext-tsum, stepW:w3:conv, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:leibniz | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:var@L555-L555 | (iv)
EDGE: bpW:w3:ext-tsum | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:var@L555-L555 | Cauchy product
EDGE: stepW:w3:conv | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:var@L556-L556 | termwise derivative
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:var@L554-L557 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w3+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:inv
KIND: step
TITLE: Inverse
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:inv@L558-L565
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:inv@L558-L565
CONTRACT_ID: stepW:w3:inv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:flow: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; rho_0 = rho_0(m) = (40 C_F)^{-1/2}, B_rho = {w : ¦¦w¦¦ < rho}; Gamma_t(w) = sum_k t^k phi_k(w) for real ¦t¦ < 2, w in B_{rho_0}; r = 2¦t¦ C_F ¦¦w¦¦^2; (vi) rho_1 = rho_0/2
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:flow (for real ¦t¦ < 2 and w in B_{rho_0} ((vi): ¦t¦ <= 1, w in B_{rho_1})); within the step: ¦t¦ <= 1, w in B_{rho_1}; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: psi(s) = Gamma_{-s}(Gamma_s(w)) is C^1 with derivative 0, so Gamma_{-t}(Gamma_t(w)) = w; injectivity and the image inclusions
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w3:est, stepW:w3:conv, stepW:w3:transport, stepW:w3:floweq, bpW:w3:ext-mvt, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w3:est | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:inv@L559-L559 | ¦¦Gamma_s(w)¦¦ <= (10/9)¦¦w¦¦
EDGE: stepW:w3:conv | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:inv@L560-L560 | C^1
EDGE: stepW:w3:transport | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:inv@L562-L562 | transport equation
EDGE: stepW:w3:floweq | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:inv@L562-L562 | flow equation
EDGE: bpW:w3:ext-mvt | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:inv@L563-L563 | zero derivative implies constant
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:inv@L558-L565 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w3+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:symplectic
KIND: theorem
TITLE: Symplecticity and gradient transport
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:symplectic@L579-L586
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:symplectic@L588-L603
CONTRACT_ID: bpW:w3:symplectic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; ¦t¦ < 2, w in B_{rho_0}, xi, eta in W; (consequence) P complex differentiable near Gamma_t(B_rho), rho <= rho_0, with Hamiltonian field X_P
SOURCE_QUANTIFIERS: for all such t, w, xi, eta; P; w in B_rho
SOURCE_CONCLUSION: Omega(D Gamma_t(w) xi, D Gamma_t(w) eta) = Omega(xi,eta); P o Gamma_t has Hamiltonian field X_{P o Gamma_t}(w) = D Gamma_t(w)^{-1} X_P(Gamma_t(w)), with values in W+ when X_P has
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:flow, bpW:w3:hamfield-def, stepW:w3:skew, stepW:w3:constform, stepW:w3:gradtrans, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:symplectic@L580-L580 | Gamma_t and rho_0
EDGE: bpW:w3:hamfield-def | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:symplectic@L583-L583 | Hamiltonian fields
EDGE: stepW:w3:skew | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:symplectic@L589-L589 | proof step
EDGE: stepW:w3:constform | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:symplectic@L593-L593 | proof step
EDGE: stepW:w3:gradtrans | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:symplectic@L598-L598 | proof step
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:symplectic@L579-L586 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:skew
KIND: step
TITLE: Skewness of $DX_F$
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:skew@L589-L592
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:skew@L589-L592
CONTRACT_ID: stepW:w3:skew
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:symplectic: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; ¦t¦ < 2, w in B_{rho_0}, xi, eta in W; (consequence) P complex differentiable near Gamma_t(B_rho), rho <= rho_0, with Hamiltonian field X_P
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:symplectic (for all such t, w, xi, eta; P; w in B_rho); within the step: y, xi, eta; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Omega(DX_F(y)xi,eta) + Omega(xi,DX_F(y)eta) = 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:F, bpW:w3:omega, bpW:w3:flow, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:F | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:skew@L591-L591 | Omega(S(.),v) = 4 frak F symmetric
EDGE: bpW:w3:omega | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:skew@L592-L592 | antisymmetry
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:skew@L590-L590 | (v): DX_F(y) xi = 3 S(y,y,xi)
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:skew@L589-L592 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:constform
KIND: step
TITLE: Constant form
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:constform@L593-L597
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:constform@L593-L597
CONTRACT_ID: stepW:w3:constform
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:symplectic: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; ¦t¦ < 2, w in B_{rho_0}, xi, eta in W; (consequence) P complex differentiable near Gamma_t(B_rho), rho <= rho_0, with Hamiltonian field X_P
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:symplectic (for all such t, w, xi, eta; P; w in B_rho); within the step: t; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: g(t) = Omega(D Gamma_t xi, D Gamma_t eta) has g' = 0 and g(0) = Omega(xi,eta)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:flow, stepW:w3:skew, bpW:w3:ext-mvt, bpW:w3:omega, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:constform@L596-L596 | (v) variational equation; D Gamma_0 = I
EDGE: stepW:w3:skew | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:constform@L596-L596 | skewness
EDGE: bpW:w3:ext-mvt | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:constform@L597-L597 | zero derivative
EDGE: bpW:w3:omega | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:constform@L594-L594 | continuity and bilinearity of the symplectic form are used to differentiate g
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:constform@L593-L597 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w3+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:gradtrans
KIND: step
TITLE: Gradient transport
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradtrans@L598-L602
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradtrans@L598-L602
CONTRACT_ID: stepW:w3:gradtrans
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:symplectic: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; ¦t¦ < 2, w in B_{rho_0}, xi, eta in W; (consequence) P complex differentiable near Gamma_t(B_rho), rho <= rho_0, with Hamiltonian field X_P
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:symplectic (for all such t, w, xi, eta; P; w in B_rho); within the step: w, v; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: D(P o Gamma_t)(w)v = Omega(D Gamma_t(w)^{-1} X_P(Gamma_t w), v); thus X_{P o Gamma_t}(w) = D Gamma_t(w)^{-1} X_P(Gamma_t w) takes values in W; if X_P takes values in W+, then so does this transported field, by invertibility of D Gamma_t(w) on W+
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:flow, stepW:w3:constform, bpW:w3:hamfield-def, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradtrans@L601-L601 | (iii) invertibility on W and W+
EDGE: stepW:w3:constform | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradtrans@L602-L602 | constant form
EDGE: bpW:w3:hamfield-def | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradtrans@L599-L599 | the defining Hamiltonian pairing of P is directly consumed
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradtrans@L598-L602 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-delta-W-w3+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:Yseries
KIND: lemma
TITLE: Power series of the integrand
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Yseries@L621-L629
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Yseries@L631-L683
CONTRACT_ID: bpW:w3:Yseries
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Y(t,w) of (bpW:w3:Ydef), rho_1 = (1/2)(40 C_F)^{-1/2}
SOURCE_QUANTIFIERS: there exist Y_j (j >= 0); then for 0 <= t <= 1 and w in B_{rho_1}
SOURCE_CONCLUSION: there are continuous (2j+3)-linear Y_j : W^{2j+3} -> W+ with sum ¦¦Y_j¦¦ rho_1^{2j+3} <= 4 C_* rho_1^3 and Y(t,w) = sum t^j Y_j(w,..,w) absolutely; int_0^1 Y(t,w) dt = sum Y_j(w,..,w)/(j+1); w -> int_0^1 Y dt has the formal power series q (q_{2j+3} = Y_j/(j+1), else 0) on B_{rho_1} and is analytic B_{rho_1} -> W+; int_0^1 Y(t,rho w) dt = rho int_0^1 Y(t,w) dt
CONSTANT_SCOPE: C_* depends only on p; rho_1 on m, p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:main-sec#data, stepW:w3:majcalc, stepW:w3:majflow, stepW:w3:majA, stepW:w3:majN, stepW:w3:majX, stepW:w3:majY, stepW:w3:majint, stepW:w3:majps, stepW:w3:majreal, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:main-sec#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Yseries@L623-L623 | the integrand Y
EDGE: stepW:w3:majcalc | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Yseries@L633-L633 | proof step
EDGE: stepW:w3:majflow | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Yseries@L645-L645 | proof step
EDGE: stepW:w3:majA | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Yseries@L648-L648 | proof step
EDGE: stepW:w3:majN | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Yseries@L655-L655 | proof step
EDGE: stepW:w3:majX | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Yseries@L662-L662 | proof step
EDGE: stepW:w3:majY | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Yseries@L666-L666 | proof step
EDGE: stepW:w3:majint | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Yseries@L672-L672 | proof step
EDGE: stepW:w3:majps | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Yseries@L676-L676 | proof step
EDGE: stepW:w3:majreal | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Yseries@L679-L679 | proof step
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Yseries@L621-L629 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:majcalc
KIND: step
TITLE: Majorant calculus
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majcalc@L633-L644
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majcalc@L633-L644
CONTRACT_ID: stepW:w3:majcalc
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:Yseries: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Y(t,w) of (bpW:w3:Ydef), rho_1 = (1/2)(40 C_F)^{-1/2}; local data: 0 <= s <= 1, 0 <= rho <= rho_1, r = 2 C_F s rho^2 (proof preamble L632)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:Yseries (there exist Y_j (j >= 0); then for 0 <= t <= 1 and w in B_{rho_1}); within the step: (t,w)-series P^i, multilinear B; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: majorant calculus: composite series have mu_{B(P^1..P^n)} <= ¦¦B¦¦ prod mu_{P^i} and sum to B(P^1(t,w),..); sums add coefficientwise; graded series and shifts
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:ext-multilinear, bpW:w3:ext-tsum, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:ext-multilinear | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majcalc@L640-L640 | norms of composites
EDGE: bpW:w3:ext-tsum | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majcalc@L641-L641 | regrouping
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majcalc@L633-L644 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w3+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:majflow
KIND: step
TITLE: The flow
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majflow@L645-L647
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majflow@L645-L647
CONTRACT_ID: stepW:w3:majflow
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:Yseries: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Y(t,w) of (bpW:w3:Ydef), rho_1 = (1/2)(40 C_F)^{-1/2}; local data: 0 <= s <= 1, 0 <= rho <= rho_1, r = 2 C_F s rho^2 (proof preamble L632)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:Yseries (there exist Y_j (j >= 0); then for 0 <= t <= 1 and w in B_{rho_1}); within the step: s, rho; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the series Gamma (shift 1) sums to Gamma_t(w) with mu_Gamma <= rho/(1-r)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:flow, bpW:w3:leibniz, stepW:w3:majcalc, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majflow@L646-L646 | Gamma_t
EDGE: bpW:w3:leibniz | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majflow@L647-L647 | (ii)
EDGE: stepW:w3:majcalc | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majflow@L646-L646 | (t,w)-series
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majflow@L645-L647 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w3+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:majA
KIND: step
TITLE: The derivative
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majA@L648-L654
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majA@L648-L654
CONTRACT_ID: stepW:w3:majA
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:Yseries: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Y(t,w) of (bpW:w3:Ydef), rho_1 = (1/2)(40 C_F)^{-1/2}; local data: 0 <= s <= 1, 0 <= rho <= rho_1, r = 2 C_F s rho^2 (proof preamble L632)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:Yseries (there exist Y_j (j >= 0); then for 0 <= t <= 1 and w in B_{rho_1}); within the step: k >= 1; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: A_{k,2k} with ¦¦A_{k,2k}¦¦ <= (2k+1)(2C_F)^k, mu_A <= 5r <= 1/16, sums to D Gamma_t(w) - I on W+
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:leibniz, stepW:w3:est, bpW:w3:ext-multilinear, bpW:w3:flow, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:leibniz | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majA@L651-L651 | (ii)
EDGE: stepW:w3:est | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majA@L653-L653 | sum (2k+1) r^k <= 5r
EDGE: bpW:w3:ext-multilinear | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majA@L653-L653 | derivative of the diagonal
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majA@L654-L654 | (i) termwise derivative
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majA@L648-L654 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w3+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:majN
KIND: step
TITLE: The inverse
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majN@L655-L661
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majN@L655-L661
CONTRACT_ID: stepW:w3:majN
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:Yseries: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Y(t,w) of (bpW:w3:Ydef), rho_1 = (1/2)(40 C_F)^{-1/2}; local data: 0 <= s <= 1, 0 <= rho <= rho_1, r = 2 C_F s rho^2 (proof preamble L632)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:Yseries (there exist Y_j (j >= 0); then for 0 <= t <= 1 and w in B_{rho_1}); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: N = sum_n (-A)^n regrouped is a graded series (shift 0) with mu_N <= 16/15 summing to D Gamma_t(w)^{-1} on W+
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w3:majA, stepW:w3:majcalc, bpW:w3:ext-tsum, bpW:w3:ext-neumann, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w3:majA | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majN@L657-L657 | mu_A <= 1/16
EDGE: stepW:w3:majcalc | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majN@L657-L657 | composite series
EDGE: bpW:w3:ext-tsum | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majN@L659-L659 | regrouping
EDGE: bpW:w3:ext-neumann | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majN@L660-L660 | Neumann series
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majN@L655-L661 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w3+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:majX
KIND: step
TITLE: The cubic field along the flow
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majX@L662-L665
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majX@L662-L665
CONTRACT_ID: stepW:w3:majX
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:Yseries: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Y(t,w) of (bpW:w3:Ydef), rho_1 = (1/2)(40 C_F)^{-1/2}; local data: 0 <= s <= 1, 0 <= rho <= rho_1, r = 2 C_F s rho^2 (proof preamble L632)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:Yseries (there exist Y_j (j >= 0); then for 0 <= t <= 1 and w in B_{rho_1}); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: 4 nabla frak z(Gamma,Gamma,Gamma) has majorant <= C_* rho^3 (1-r)^{-3}, sums to X_{Z'}(Gamma_t w), shift 3
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:quartic, stepW:w3:majflow, stepW:w3:majcalc, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majX@L663-L663 | 4 nabla frak z trilinear of norm <= C_*
EDGE: stepW:w3:majflow | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majX@L664-L664 | the series Gamma
EDGE: stepW:w3:majcalc | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majX@L664-L664 | composites
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majX@L662-L665 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w3+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:majY
KIND: step
TITLE: The integrand
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majY@L666-L671
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majY@L666-L671
CONTRACT_ID: stepW:w3:majY
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:Yseries: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Y(t,w) of (bpW:w3:Ydef), rho_1 = (1/2)(40 C_F)^{-1/2}; local data: 0 <= s <= 1, 0 <= rho <= rho_1, r = 2 C_F s rho^2 (proof preamble L632)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:Yseries (there exist Y_j (j >= 0); then for 0 <= t <= 1 and w in B_{rho_1}); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the composite series cal Y sums to Y(t,w), has shift 3 and mu_Y(1,rho_1) <= 4 C_* rho_1^3; Y_j = cal Y_{j,2j+3}
CONSTANT_SCOPE: C_* depends only on p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w3:majN, stepW:w3:majX, bpW:w3:main-sec#data, stepW:w3:majcalc, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w3:majN | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majY@L668-L668 | N
EDGE: stepW:w3:majX | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majY@L668-L668 | the cubic field along the flow
EDGE: bpW:w3:main-sec#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majY@L669-L669 | Y(t,w)
EDGE: stepW:w3:majcalc | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majY@L667-L670 | the bilinear application composite and subtraction use the composite-series identity and product majorant bound
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majY@L666-L671 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-delta3-W-w3+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:majint
KIND: step
TITLE: Integrate in $t$
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majint@L672-L675
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majint@L672-L675
CONTRACT_ID: stepW:w3:majint
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:Yseries: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Y(t,w) of (bpW:w3:Ydef), rho_1 = (1/2)(40 C_F)^{-1/2}; local data: 0 <= s <= 1, 0 <= rho <= rho_1, r = 2 C_F s rho^2 (proof preamble L632)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:Yseries (there exist Y_j (j >= 0); then for 0 <= t <= 1 and w in B_{rho_1}); within the step: w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: termwise integration in t: int_0^1 Y dt = sum Y_j(w,..,w)/(j+1)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w3:majY, bpW:w3:ext-integral, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w3:majY | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majint@L674-L674 | the bounds on Y_j
EDGE: bpW:w3:ext-integral | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majint@L674-L674 | termwise integration
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majint@L672-L675 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w3+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:majps
KIND: step
TITLE: Power series
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majps@L676-L678
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majps@L676-L678
CONTRACT_ID: stepW:w3:majps
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:Yseries: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Y(t,w) of (bpW:w3:Ydef), rho_1 = (1/2)(40 C_F)^{-1/2}; local data: 0 <= s <= 1, 0 <= rho <= rho_1, r = 2 C_F s rho^2 (proof preamble L632)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:Yseries (there exist Y_j (j >= 0); then for 0 <= t <= 1 and w in B_{rho_1}); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: sum ¦¦q_n¦¦ rho_1^n < infinity, so the formal power series and analyticity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w3:majY, bpW:w3:ext-series, stepW:w3:majint, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w3:majY | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majps@L677-L677 | sum ¦¦Y_j¦¦ rho_1^{2j+3}
EDGE: bpW:w3:ext-series | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majps@L677-L677 | power series give analyticity
EDGE: stepW:w3:majint | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majps@L677-L678 | the preceding termwise integral identity identifies the diagonal series with coefficients q with the integral whose analyticity is asserted
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majps@L676-L678 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-delta3-W-w3+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:majreal
KIND: step
TITLE: Reality
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majreal@L679-L682
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majreal@L679-L682
CONTRACT_ID: stepW:w3:majreal
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:Yseries: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Y(t,w) of (bpW:w3:Ydef), rho_1 = (1/2)(40 C_F)^{-1/2}; local data: 0 <= s <= 1, 0 <= rho <= rho_1, r = 2 C_F s rho^2 (proof preamble L632)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:Yseries (there exist Y_j (j >= 0); then for 0 <= t <= 1 and w in B_{rho_1}); within the step: t real; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Y(t, rho w) = rho Y(t,w) and rho commutes with the t-integral
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:flow, bpW:w3:hamfield-def, bpW:w3:ext-integral, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majreal@L680-L680 | (iv) reality of Gamma_t
EDGE: bpW:w3:hamfield-def | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majreal@L681-L681 | X_{Z'} commutes with rho
EDGE: bpW:w3:ext-integral | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majreal@L682-L682 | continuous R-linear maps commute with the integral
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majreal@L679-L682 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w3+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:main
KIND: theorem
TITLE: Analytic partial Birkhoff normal form; P96-W Main Proposition for $J=\{1,2\}$
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main@L687-L705
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main@L707-L756
CONTRACT_ID: bpW:w3:main
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Gamma = Gamma_1, rho_1 = rho_1(m) = (1/2)(40 C_F(m))^{-1/2}; H = Lambda + G; K = H o Gamma - Lambda - bar G - G^nor on B_{rho_1}
SOURCE_QUANTIFIERS: for all w in B_{rho_1} ((iv): w in B_{rho_1} cap W+)
SOURCE_CONCLUSION: (i) K is analytic on B_{rho_1} and real, ¦K(w)¦ <= C_K ¦¦w¦¦^6, C_K = 10 C_* C_F; (ii) K in A(B_{rho_1}): X_K is analytic B_{rho_1} -> W+, real, ¦¦X_K(w)¦¦_+ <= C'_K ¦¦w¦¦^5, C'_K = 66 C_* C_F; X_K^R = Z^{-1} X_K o Z is real analytic B^E_{r_1} -> E_{a,p+1} (r_1 = rho_1/sqrt2) and equals (d_p K^R, -d_q K^R) for K^R = K o Z; (iii) bar G = (1/2)<AI,I> + <BI,Z> with the corrected coefficients, G^nor depends only on hat w, ¦G^nor¦ <= (C_*/4)¦¦hat w¦¦^4, both in A(W) with cubic fields bounded by C_*¦¦w¦¦^3 (C_*¦¦hat w¦¦^3); (iv) for w in B_{rho_1} cap W+, Gamma(w) in W+ and D Gamma(w)[X_Lambda(w) + X_{bar G}(w) + X_{G^nor}(w) + X_K(w)] = X_H(Gamma(w))
CONSTANT_SCOPE: C_K, C'_K, rho_1 depend on m and p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:main-sec#data, bpW:w3:flow, bpW:w3:hamfield-def, stepW:w3:Kanalytic, stepW:w3:K1, stepW:w3:K2, stepW:w3:XK1, stepW:w3:XK2, stepW:w3:XKconcl, stepW:w3:iii, stepW:w3:conj, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:main-sec#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main@L689-L689 | H = Lambda + G
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main@L688-L688 | Gamma = Gamma_1
EDGE: bpW:w3:hamfield-def | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main@L693-L693 | the class A
EDGE: stepW:w3:Kanalytic | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main@L710-L710 | proof step
EDGE: stepW:w3:K1 | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main@L714-L714 | proof step
EDGE: stepW:w3:K2 | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main@L718-L718 | proof step
EDGE: stepW:w3:XK1 | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main@L724-L724 | proof step
EDGE: stepW:w3:XK2 | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main@L732-L732 | proof step
EDGE: stepW:w3:XKconcl | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main@L742-L742 | proof step
EDGE: stepW:w3:iii | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main@L747-L747 | proof step
EDGE: stepW:w3:conj | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main@L749-L749 | proof step
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main@L687-L705 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:Kanalytic
KIND: step
TITLE: Analyticity and reality
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Kanalytic@L710-L713
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Kanalytic@L710-L713
CONTRACT_ID: stepW:w3:Kanalytic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:main: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Gamma = Gamma_1, rho_1 = rho_1(m) = (1/2)(40 C_F(m))^{-1/2}; H = Lambda + G; K = H o Gamma - Lambda - bar G - G^nor on B_{rho_1}; local data: Z' = bar G - G^tan; K_1 = G o Gamma - G, K_2 = Lambda o Gamma - Lambda - Z' (proof preamble L708-L709)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:main (for all w in B_{rho_1} ((iv): w in B_{rho_1} cap W+)); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: K is analytic on B_{rho_1} and real
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:flow, bpW:w3:ext-series, bpW:w3:Lambda, bpW:w3:quartic, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Kanalytic@L712-L712 | (i) Gamma analytic; (iv) reality
EDGE: bpW:w3:ext-series | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Kanalytic@L712-L712 | compositions
EDGE: bpW:w3:Lambda | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Kanalytic@L711-L711 | Lambda a continuous polynomial
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Kanalytic@L711-L711 | G, bar G, G^nor polynomials
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Kanalytic@L710-L713 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w3+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:K1
KIND: step
TITLE: The bound for $K_1$
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K1@L714-L717
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K1@L714-L717
CONTRACT_ID: stepW:w3:K1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:main: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Gamma = Gamma_1, rho_1 = rho_1(m) = (1/2)(40 C_F(m))^{-1/2}; H = Lambda + G; K = H o Gamma - Lambda - bar G - G^nor on B_{rho_1}; local data: Z' = bar G - G^tan; K_1 = G o Gamma - G, K_2 = Lambda o Gamma - Lambda - Z' (proof preamble L708-L709)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:main (for all w in B_{rho_1} ((iv): w in B_{rho_1} cap W+)); within the step: w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦K_1(w)¦ = ¦G(Gamma w) - G(w)¦ <= 5 C_* C_F ¦¦w¦¦^6
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:ext-mvt, bpW:w3:flow, bpW:w3:quartic, bpW:w3:omega, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:ext-mvt | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K1@L716-L716 | mean value inequality on the segment
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K1@L717-L717 | (iii) estimates
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K1@L716-L716 | ¦¦X_G(y)¦¦_+ <= C_*¦¦y¦¦^3
EDGE: bpW:w3:omega | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K1@L716-L716 | DG(y)v = Omega(X_G(y),v)
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K1@L714-L717 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w3+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:K2
KIND: step
TITLE: The bound for $K_2$
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K2@L718-L723
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K2@L718-L723
CONTRACT_ID: stepW:w3:K2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:main: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Gamma = Gamma_1, rho_1 = rho_1(m) = (1/2)(40 C_F(m))^{-1/2}; H = Lambda + G; K = H o Gamma - Lambda - bar G - G^nor on B_{rho_1}; local data: Z' = bar G - G^tan; K_1 = G o Gamma - G, K_2 = Lambda o Gamma - Lambda - Z' (proof preamble L708-L709)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:main (for all w in B_{rho_1} ((iv): w in B_{rho_1} cap W+)); within the step: w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: h(t) = Lambda(Gamma_t w) - Lambda(w) - t Z'(w) has h(0) = 0, h'(t) = Z'(Gamma_t w) - Z'(w), ¦h'(t)¦ <= 5 C_* C_F t ¦¦w¦¦^6, so ¦K_2(w)¦ <= 5 C_* C_F ¦¦w¦¦^6; with K_1, (i)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:flow, bpW:w3:homological, stepW:w3:K1, stepW:w3:Kanalytic, bpW:w3:ext-integral, bpW:w3:quartic, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K2@L720-L720 | (ii) flow equation
EDGE: bpW:w3:homological | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K2@L720-L720 | DLambda . X_F = Z' at Gamma_t w
EDGE: stepW:w3:K1 | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K2@L722-L722 | the same mean value argument
EDGE: stepW:w3:Kanalytic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K2@L723-L723 | (i) analyticity part
EDGE: bpW:w3:ext-integral | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K2@L723-L723 | integrating the derivative bound on h gives the K2 estimate
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K2@L722-L722 | the derivative bound for Z prime requires its quartic smoothing bound
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K2@L718-L723 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w3+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:XK1
KIND: step
TITLE: The field of $K_1$
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK1@L724-L731
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK1@L724-L731
CONTRACT_ID: stepW:w3:XK1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:main: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Gamma = Gamma_1, rho_1 = rho_1(m) = (1/2)(40 C_F(m))^{-1/2}; H = Lambda + G; K = H o Gamma - Lambda - bar G - G^nor on B_{rho_1}; local data: Z' = bar G - G^tan; K_1 = G o Gamma - G, K_2 = Lambda o Gamma - Lambda - Z' (proof preamble L708-L709)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:main (for all w in B_{rho_1} ((iv): w in B_{rho_1} cap W+)); within the step: w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: X_{K_1}(w) = D Gamma^{-1} X_G(Gamma w) - X_G(w), ¦¦X_{K_1}(w)¦¦_+ <= 44 C_* C_F ¦¦w¦¦^5, analytic into W+
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:symplectic, bpW:w3:forms, bpW:w3:flow, bpW:w3:ext-series, bpW:w3:quartic, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:symplectic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK1@L725-L725 | gradient transport
EDGE: bpW:w3:forms | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK1@L727-L727 | Lipschitz bound d = 4
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK1@L727-L727 | (iii)
EDGE: bpW:w3:ext-series | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK1@L730-L730 | analyticity of D(Gamma - id), inversion
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK1@L728-L728 | the cubic field bound for X_G supplies the premise of the transport estimate
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK1@L724-L731 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w3+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:XK2
KIND: step
TITLE: The field of $K_2$
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK2@L732-L741
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK2@L732-L741
CONTRACT_ID: stepW:w3:XK2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:main: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Gamma = Gamma_1, rho_1 = rho_1(m) = (1/2)(40 C_F(m))^{-1/2}; H = Lambda + G; K = H o Gamma - Lambda - bar G - G^nor on B_{rho_1}; local data: Z' = bar G - G^tan; K_1 = G o Gamma - G, K_2 = Lambda o Gamma - Lambda - Z' (proof preamble L708-L709)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:main (for all w in B_{rho_1} ((iv): w in B_{rho_1} cap W+)); within the step: w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: K_2(w) = int_0^1 (Z'(Gamma_t w) - Z'(w)) dt, X_{K_2}(w) = int_0^1 Y(t,w) dt with ¦¦X_{K_2}(w)¦¦_+ <= 22 C_* C_F ¦¦w¦¦^5, analytic B_{rho_1} -> W+
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:ext-integral, stepW:w3:K2, bpW:w3:symplectic, bpW:w3:main-sec#data, stepW:w3:XK1, bpW:w3:Yseries, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:ext-integral | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK2@L733-L733 | FTC and differentiation under the integral
EDGE: stepW:w3:K2 | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK2@L733-L733 | h'(t)
EDGE: bpW:w3:symplectic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK2@L735-L735 | gradient transport
EDGE: bpW:w3:main-sec#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK2@L736-L736 | Y of (bpW:w3:Ydef)
EDGE: stepW:w3:XK1 | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK2@L736-L736 | the same bound
EDGE: bpW:w3:Yseries | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK2@L737-L737 | D_w Y bounded; analyticity of the integral
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK2@L732-L741 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w3+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:XKconcl
KIND: step
TITLE: Conclusion of (ii)
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XKconcl@L742-L746
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XKconcl@L742-L746
CONTRACT_ID: stepW:w3:XKconcl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:main: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Gamma = Gamma_1, rho_1 = rho_1(m) = (1/2)(40 C_F(m))^{-1/2}; H = Lambda + G; K = H o Gamma - Lambda - bar G - G^nor on B_{rho_1}; local data: Z' = bar G - G^tan; K_1 = G o Gamma - G, K_2 = Lambda o Gamma - Lambda - Z' (proof preamble L708-L709)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:main (for all w in B_{rho_1} ((iv): w in B_{rho_1} cap W+)); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (ii): X_K = X_{K_1} + X_{K_2}, 44 + 22 = 66, analytic; reality; the real restriction and (d_p K^R, -d_q K^R)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w3:XK1, stepW:w3:XK2, bpW:w3:hamfield-def, bpW:w3:real-restrict, bpW:w3:hamfield-def#hamilton, bpW:w3:coords, stepW:w3:Kanalytic, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w3:XK1 | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XKconcl@L743-L743 | X_{K_1}
EDGE: stepW:w3:XK2 | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XKconcl@L743-L743 | X_{K_2}
EDGE: bpW:w3:hamfield-def | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XKconcl@L744-L744 | reality of the field
EDGE: bpW:w3:real-restrict | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XKconcl@L744-L744 | real restriction
EDGE: bpW:w3:hamfield-def#hamilton | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XKconcl@L745-L745 | Z^{-1} X_K = (d_p K, -d_q K) on real points
EDGE: bpW:w3:coords | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XKconcl@L746-L746 | ¦¦Zx¦¦ <= sqrt2 ¦¦x¦¦_E
EDGE: stepW:w3:Kanalytic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XKconcl@L744-L744 | reality of K from part (i) supplies the reality premise of the Hamiltonian-field argument
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XKconcl@L742-L746 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w3+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:iii
KIND: step
TITLE: (iii)
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:iii@L747-L748
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:iii@L747-L748
CONTRACT_ID: stepW:w3:iii
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:main: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Gamma = Gamma_1, rho_1 = rho_1(m) = (1/2)(40 C_F(m))^{-1/2}; H = Lambda + G; K = H o Gamma - Lambda - bar G - G^nor on B_{rho_1}; local data: Z' = bar G - G^tan; K_1 = G o Gamma - G, K_2 = Lambda o Gamma - Lambda - Z' (proof preamble L708-L709)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:main (for all w in B_{rho_1} ((iv): w in B_{rho_1} cap W+)); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iii) from Lemmas bpW:w3:quartic and bpW:w3:quartic-ident
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:quartic, bpW:w3:quartic-ident, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:iii@L748-L748 | forms and bounds
EDGE: bpW:w3:quartic-ident | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:iii@L748-L748 | bar G, G^nor
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:iii@L747-L748 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w3+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:conj
KIND: step
TITLE: Conjugacy
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L749-L755
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L749-L755
CONTRACT_ID: stepW:w3:conj
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:main: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Gamma = Gamma_1, rho_1 = rho_1(m) = (1/2)(40 C_F(m))^{-1/2}; H = Lambda + G; K = H o Gamma - Lambda - bar G - G^nor on B_{rho_1}; local data: Z' = bar G - G^tan; K_1 = G o Gamma - G, K_2 = Lambda o Gamma - Lambda - Z' (proof preamble L708-L709)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:main (for all w in B_{rho_1} ((iv): w in B_{rho_1} cap W+)); within the step: w in B_{rho_1} cap W+; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iv): Gamma(w) in W+ and D Gamma(w)[X_Lambda + X_{bar G} + X_{G^nor} + X_K](w) = X_H(Gamma(w))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:flow, bpW:w3:Lambda, bpW:w3:symplectic, bpW:w3:omega, stepW:w3:XKconcl, bpW:w3:quartic, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L750-L750 | Gamma - id into W+
EDGE: bpW:w3:Lambda | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L751-L751 | DH(y)u = Omega(X_H(y),u) on W+
EDGE: bpW:w3:symplectic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L752-L752 | gradient transport
EDGE: bpW:w3:omega | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L755-L755 | nondegeneracy
EDGE: stepW:w3:XKconcl | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L754-L754 | X_K
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L751-L754 | the quartic Hamiltonian fields supply the G, bar G and G^nor derivative pairings in DH and the transformed Hamiltonian
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L749-L755 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-delta3-W-w3+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:gamma-real
KIND: corollary
TITLE: Real change of coordinates
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:gamma-real@L780-L794
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:gamma-real@L796-L806
CONTRACT_ID: bpW:w3:gamma-real
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; r_1 = rho_1/sqrt2, B^E_r = {x in E_{a,p} : ¦¦x¦¦_E < r}; Gamma^R = Z^{-1} o Gamma o Z
SOURCE_QUANTIFIERS: x in B^E_{r_1}
SOURCE_CONCLUSION: Gamma^R : B^E_{r_1} -> E_{a,p} is well defined and (i) real analytic with the real power series of terms Z^{-1} Phi_k(Z.,..,Z.); (ii) ¦¦Gamma^R(x) - x¦¦_{E_{a,p+1}} <= 6 sqrt2 C_F ¦¦x¦¦_E^3 and Gamma^R(B^E_{r_1}) subset B^E_{2r_1}; (iii) symplectic for sum dq ^ dp, injective, inverse Z^{-1} Gamma_{-1} Z on its image, image contains B^E_{r_1/2}; (iv) H(Gamma^R x) = Lambda(x) + bar G(x) + G^nor(x) + K(Zx) with bar G = (1/2)<AI,I> + <BI,Z>, I_j = (q_j^2+p_j^2)/2
CONSTANT_SCOPE: C_F, r_1 depend on m and p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:flow, bpW:w3:coords, bpW:w3:leibniz, bpW:w3:ext-series, bpW:w3:omega, bpW:w3:symplectic, bpW:w3:main, bpW:w3:quartic-ident, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:gamma-real@L797-L797 | (iii), (iv), (vi)
EDGE: bpW:w3:coords | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:gamma-real@L798-L798 | Z and real points
EDGE: bpW:w3:leibniz | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:gamma-real@L799-L799 | (iii) reality of Phi_k
EDGE: bpW:w3:ext-series | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:gamma-real@L801-L801 | analyticity over R
EDGE: bpW:w3:omega | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:gamma-real@L802-L802 | the real form
EDGE: bpW:w3:symplectic | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:gamma-real@L803-L803 | symplecticity
EDGE: bpW:w3:main | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:gamma-real@L805-L805 | (iv) the normal form
EDGE: bpW:w3:quartic-ident | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:gamma-real@L805-L805 | bar G on real points
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:gamma-real@L780-L794 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:transport-tori
KIND: corollary
TITLE: Invariant tori are transported
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori@L810-L817
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori@L819-L823
CONTRACT_ID: bpW:w3:transport-tori
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; nu in R^2; Psi : R^2 -> B_{rho_1} cap W+ differentiable into W with D Psi(theta) nu = X_{H'}(Psi(theta)), X_{H'} = X_Lambda + X_{bar G} + X_{G^nor} + X_K; for the last claim Psi real (rho Psi = Psi)
SOURCE_QUANTIFIERS: for all such nu, Psi; all theta; j >= 1
SOURCE_CONCLUSION: Gamma o Psi takes values in W+ and D(Gamma o Psi)(theta) nu = X_H(Gamma o Psi(theta)); if Psi is real, (Q,P) = Z^{-1} Gamma o Psi satisfies D_nu Q_j = lambda_j P_j, D_nu P_j = -lambda_j Q_j - T(Q,Q,Q)_j, the coefficient system (bpW:w0:coeffsys) (T = G_q for a > 0)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:main, bpW:w3:Lambda, bpW:w3:quartic-ident, bpW:w0:eqmotion, bpW:w0:basis#lam, bpW:w0:Gq#cubicGrad, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:main | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori@L820-L820 | (iv) conjugacy
EDGE: bpW:w3:Lambda | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori@L822-L822 | X_Lambda on real points
EDGE: bpW:w3:quartic-ident | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori@L822-L822 | Z^{-1} X_G = (0,-T(q,q,q))
EDGE: bpW:w0:eqmotion | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori@L816-L816 | the coefficient system
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori@L815-L815 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori@L816-L816 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori@L810-L817 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3#data
KIND: definition
TITLE: W3 standing data (a, p, J)
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3@L23-L27
PROOF_SOURCE: -
CONTRACT_ID: bpW:w3#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: fixes, throughout Part W3, a >= 0 and p >= 1/2 (headline a = p = 1), the tangential modes J = {1,2} and normal modes j >= 3; constants depend on m, a, p as listed in section bpW:w3:constants
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:mass
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:mass | blueprint-W/parts/w3-birkhoff.tex#bpW:w3@L23-L23 | Standing assumption m > 0 in force
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Unlabelled 'Standing data' paragraph (SPEC hypothesis packages): its premise p >= 1/2 is used by Lemma bpW:w3:Lambda and every bound through C_* = K_{p+1/2}^2/pi; it is recorded in the SOURCE_HYPOTHESES of each W3 result.

NODE: bpW:w3:hamfield-def#hamilton
KIND: claim
TITLE: Hamilton's equations and reality of X_P
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:hamfield-def@L164-L167
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:hamfield-def@L164-L167
CONTRACT_ID: bpW:w3:hamfield-def#hamilton
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; P as in Definition bpW:w3:hamfield-def
SOURCE_QUANTIFIERS: real points; w, v
SOURCE_CONCLUSION: on real points Z^{-1} X_P = (d_p P, -d_q P), the convention of Definition bpW:w0:eqmotion; if P is real then X_P o rho = rho o X_P
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:hamfield-def, bpW:w3:omega, bpW:w0:eqmotion, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:hamfield-def | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:hamfield-def@L164-L164 | the Hamiltonian field X_P
EDGE: bpW:w3:omega | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:hamfield-def@L165-L165 | Omega(Zx,Zx') = sum (q p' - p q') and Omega(rho w, rho w') = conj Omega
EDGE: bpW:w0:eqmotion | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:hamfield-def@L165-L165 | the sign convention of Hamilton's equations
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:hamfield-def@L164-L167 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: PARTIAL
LEAN_REF: KAM.Wave.IsBirkClassA.field_rho, KAM.Wave.birkZinv_birkQuartX_birkZ (KAM/Wave/Birkhoff/HamClass.lean, KAM/Wave/Birkhoff/QuartIdent.lean)
LEAN_NOTE: W3-SETTING-DIVF audit 1 PASS for IsBirkClassA.field_rho; covered: X_P o rho = rho o X_P for class-A Hamiltonians; not covered: the general real-point identity Z^{-1} X_P = (d_p P, -d_q P) (proved only for P = G via birkZinv_birkQuartX_birkZ) and reality of the field for real P outside class A
NOTE: Unlabelled paragraph after Definition bpW:w3:hamfield-def, cited as "paragraph after Definition bpW:w3:hamfield-def" in Steps stepW:w3:XG and stepW:w3:XKconcl.

NODE: bpW:w3:quartic-sec#data
KIND: definition
TITLE: Two-sided quartic coefficients, divisors, pairing, tangential set
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-sec@L224-L230
PROOF_SOURCE: -
CONTRACT_ID: bpW:w3:quartic-sec#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; x in (Z\0)^4
SOURCE_QUANTIFIERS: x
SOURCE_CONCLUSION: defines ¦x¦, w_x = w_{x_1} w_{x_2} w_{x_3} w_{x_4}, frak g_x = g_¦x¦/sqrt(lambda_¦x_1¦ .. lambda_¦x_4¦), delta_x = lambda'_{x_1} + .. + lambda'_{x_4}; x paired iff a permutation of (r,-r,s,-s) (then delta_x = 0); T = {x : min_t ¦x_t¦ <= 2} (at least one tangential index)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:quartic-coeff, bpW:w3:space, bpW:w0:basis#lam, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-sec@L228-L228 | g from Lemma bpW:w0n:quartic-coeff
EDGE: bpW:w3:space | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-sec@L227-L227 | lambda'_l = sgn(l) lambda_¦l¦
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-sec@L226-L226 | lambda occurs directly here (frozen lam)
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-sec@L224-L230 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.birkAbs, KAM.Wave.birkAtom, KAM.Wave.birkG, KAM.Wave.birkDivisor, KAM.Wave.birkPaired, KAM.Wave.birkTanSet, KAM.Wave.birkBarSet (KAM/Wave/Birkhoff/Reindex.lean, KAM/Wave/Birkhoff/QuartGrad.lean, KAM/Wave/Birkhoff/QuartPaired.lean)
LEAN_NOTE: definition formalized by W3-SETTING; W3-SETTING-DIVF audit 1 PASS (definition ledger rows; all literal formulas); (mapping inferred)
NOTE: Unlabelled prose L224-L230 fixing notation consumed throughout W3 (SPEC section-data rule).

NODE: bpW:w3:main-sec#data
KIND: definition
TITLE: H = Lambda + G on W and the integrand Y(t,w)
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main-sec@L608-L619
PROOF_SOURCE: -
CONTRACT_ID: bpW:w3:main-sec#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}
SOURCE_QUANTIFIERS: 0 <= t <= 1, w in B_{rho_1}
SOURCE_CONCLUSION: defines H = Lambda + G on W (on real points the Hamiltonian of Definition bpW:w0:H), X_H = X_Lambda + X_G on W+ with values in W, and (bpW:w3:Ydef) Y(t,w) = D Gamma_t(w)^{-1} X_{Z'}(Gamma_t w) - X_{Z'}(w) in W+, Z' = bar G - G^tan, rho_1 = (1/2)(40 C_F)^{-1/2}, D Gamma_t(w)^{-1} the inverse on W+
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:Lambda, bpW:w3:quartic, bpW:w0:H, bpW:w3:homological, bpW:w3:flow, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:Lambda | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main-sec@L608-L608 | Lambda finite, X_Lambda on W+
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main-sec@L608-L608 | G finite, X_G
EDGE: bpW:w0:H | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main-sec@L609-L609 | the Hamiltonian on real points
EDGE: bpW:w3:homological | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main-sec@L615-L615 | Z' = bar G - G^tan and X_{Z'}
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main-sec@L617-L617 | (iii) the inverse of D Gamma_t on W+
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main-sec@L608-L619 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Unlabelled prose L608-L619 (with the display bpW:w3:Ydef) fixing H, X_H and Y used by Lemma bpW:w3:Yseries and Theorem bpW:w3:main (SPEC section-data rule).

NODE: stepW:w3:divisor#curvature
KIND: step
TITLE: Curvature and comparison for the divisor bound
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L336-L338
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L336-L338
CONTRACT_ID: stepW:w3:divisor#curvature
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0 fixed; x as in bpW:w3:divisor; A <= B <= C <= D are its sorted positive absolute indices (the source writes a,b,c,d); f(s)=sqrt(s^2+m), lambda_k=f(k); beta=m/(27 lambda_A^3)
SOURCE_QUANTIFIERS: for every such m,x and every s >= 0
SOURCE_CONCLUSION: f_prime(s)=s/f(s) is increasing; f_second(s)=m/f(s)^3 is positive and decreasing on s >= 0; m <= lambda_A^2 gives 0 < beta <= 1/(27 lambda_A)
CONSTANT_SCOPE: the numerical constant 1/27 is absolute; beta depends on m and A
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:mass, bpW:w0:basis#lam, bpW:w0:basis#lambda-facts
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:mass | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L337-L337 | positivity of the second derivative uses m > 0 itself
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L337-L338 | f(k)=lambda_k and beta explicitly use the frozen frequencies
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L337-L337 | the recalled monotonicity of f prime is the earlier frequency fact
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: new+sol-review-W-w3
REVIEWER: sol-delta-W-w3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.birkL, KAM.Wave.lam_eq_birkL, KAM.Wave.birkL_second_diff, KAM.Wave.birkDelta_mono, KAM.Wave.birkDelta_ge, KAM.Wave.birkL_incr_mono, KAM.Wave.birkL_incr_sub (KAM/Wave/Birkhoff/DivisorReal.lean)
LEAN_NOTE: step of PROVED parent bpW:w3:divisor; W3-SETTING-DIVF audit 1 PASS; route deviation: the derivative statements on f' and f'' are replaced by exact discrete increment/second-difference inequalities, not formalized as stated; Lean route differs: discrete second differences replace the derivative facts
NOTE: This separates the quantitative preamble used by the sign cases; it is not an extra assumption. The symbol A here is the smallest mode, not the exponential weight a.

NODE: bpW:w3:transport-tori-weak
KIND: corollary
TITLE: Weak invariance is transported
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori-weak@L831-L842
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori-weak@L844-L866
CONTRACT_ID: bpW:w3:transport-tori-weak
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; for w in W, X_Lambda(w) = (-i lambda'_l w_l)_{l != 0} in W_{a,p-1}; nu in R^2; Psi : R^2 -> B_{rho_1} differentiable as a map into W with D Psi(theta) nu = X_Lambda(Psi(theta)) + X_{bar G}(Psi(theta)) + X_{G^nor}(Psi(theta)) + X_K(Psi(theta)) in W_{a,p-1} for every theta
SOURCE_QUANTIFIERS: for all nu, Psi as stated; for every theta
SOURCE_CONCLUSION: Psi(theta) in W+ with ¦¦Psi(theta)¦¦_+ <= ¦¦D Psi(theta) nu¦¦ + C_* ¦¦Psi(theta)¦¦^3 + C'_K ¦¦Psi(theta)¦¦^5 for every theta, and all conclusions of Corollary bpW:w3:transport-tori hold: Gamma o Psi takes values in W+, D(Gamma o Psi)(theta) nu = X_H(Gamma o Psi(theta)) in W, and for real Psi the coefficient system (bpW:w0:coeffsys) holds for (Q,P) = Z^{-1} Gamma o Psi
CONSTANT_SCOPE: C_*, C'_K as in Theorem bpW:w3:main (m, p)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:Lambda, bpW:w3:quartic, bpW:w3:main, bpW:w3:transport-tori, bpW:w0:eqmotion, bpW:w0:basis#lam, stepW:w3:wk-lin, stepW:w3:wk-reg, stepW:w3:wk-transport, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:Lambda | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori-weak@L833-L833 | X_Lambda extends the linear field of Lemma bpW:w3:Lambda
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori-weak@L835-L835 | the fields X_{bar G}, X_{G^nor}
EDGE: bpW:w3:main | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori-weak@L835-L835 | the field X_K and C'_K
EDGE: bpW:w3:transport-tori | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori-weak@L838-L838 | its conclusions are asserted for Psi
EDGE: bpW:w0:eqmotion | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori-weak@L840-L840 | the coefficient system (bpW:w0:coeffsys)
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori-weak@L832-L832 | lambda'_l = sgn(l) lambda_¦l¦ occurs directly here (frozen lam)
EDGE: stepW:w3:wk-lin | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori-weak@L845-L845 | proof step
EDGE: stepW:w3:wk-reg | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori-weak@L850-L850 | proof step
EDGE: stepW:w3:wk-transport | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori-weak@L859-L859 | proof step
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori-weak@L831-L842 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W-w2+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: New corollary of the revised W3 (wave 2); consumed by W6/W8 (KAM tori invariant only in W_{a,p-1}).

NODE: stepW:w3:wk-lin
KIND: step
TITLE: The linear field on W
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-lin@L845-L849
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-lin@L845-L849
CONTRACT_ID: stepW:w3:wk-lin
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:transport-tori-weak: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; for w in W, X_Lambda(w) = (-i lambda'_l w_l)_{l != 0} in W_{a,p-1}; nu in R^2; Psi : R^2 -> B_{rho_1} differentiable as a map into W with D Psi(theta) nu = X_Lambda(Psi(theta)) + X_{bar G}(Psi(theta)) + X_{G^nor}(Psi(theta)) + X_K(Psi(theta)) in W_{a,p-1} for every theta
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:transport-tori-weak (all such nu, Psi; every theta); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: X_Lambda : W -> W_{a,p-1} is bounded with norm <= sqrt(1+m) and agrees with Lemma bpW:w3:Lambda on W+; the other three fields take values in W+ subset W subset W_{a,p-1} with norm-one inclusions
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:diag, bpW:w3:Lambda, bpW:w3:main, bpW:w1:embed, bpW:w0:mass, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:diag | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-lin@L846-L846 | (i) with p-1 in place of p and r = 1
EDGE: bpW:w3:Lambda | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-lin@L848-L848 | agreement on W+
EDGE: bpW:w3:main | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-lin@L849-L849 | (ii), (iii): the fields of bar G, G^nor, K take values in W+
EDGE: bpW:w1:embed | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-lin@L849-L849 | norm-one inclusions
EDGE: bpW:w0:mass | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-lin@L847-L847 | m > 0 in the sqrt(1+m) multiplier bound
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-lin@L845-L849 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W-w2+sol-delta5-W-w3+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:wk-reg
KIND: step
TITLE: Regularity of the torus points
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-reg@L850-L858
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-reg@L850-L858
CONTRACT_ID: stepW:w3:wk-reg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:transport-tori-weak: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; for w in W, X_Lambda(w) = (-i lambda'_l w_l)_{l != 0} in W_{a,p-1}; nu in R^2; Psi : R^2 -> B_{rho_1} differentiable as a map into W with D Psi(theta) nu = X_Lambda(Psi(theta)) + X_{bar G}(Psi(theta)) + X_{G^nor}(Psi(theta)) + X_K(Psi(theta)) in W_{a,p-1} for every theta; local data: w = Psi(theta)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:transport-tori-weak (all such nu, Psi; every theta); m > 0 fixed (standing assumption); within the step: theta
SOURCE_CONCLUSION: X_Lambda(w) = D Psi(theta) nu - X_{bar G}(w) - X_{G^nor}(w) - X_K(w) lies in W with norm <= ¦¦D Psi(theta) nu¦¦ + C_* ¦¦w¦¦^3 + C'_K ¦¦w¦¦^5; hence w in W+ with ¦¦w¦¦_+ <= ¦¦X_Lambda(w)¦¦
CONSTANT_SCOPE: C_*, C'_K as in Theorem bpW:w3:main
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:main, bpW:w3:quartic, bpW:w0:basis#lambda-facts, bpW:w1:diag, stepW:w3:wk-lin, bpW:w0:basis#lam, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:main | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-reg@L853-L853 | the bound on X_K
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-reg@L854-L854 | the bound C_* ¦¦w¦¦^3 for bar frak G + frak G^nor (disjoint coefficient sets)
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-reg@L856-L856 | ¦l¦ <= lambda_¦l¦
EDGE: bpW:w1:diag | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-reg@L857-L857 | (i) with r = -1
EDGE: stepW:w3:wk-lin | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-reg@L852-L852 | X_Lambda(w) is defined in W_{a,p-1}
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-reg@L856-L856 | lambda occurs directly here (frozen lam)
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-reg@L850-L858 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W-w2+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:wk-transport
KIND: step
TITLE: Transport
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-transport@L859-L865
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-transport@L859-L865
CONTRACT_ID: stepW:w3:wk-transport
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:transport-tori-weak: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; for w in W, X_Lambda(w) = (-i lambda'_l w_l)_{l != 0} in W_{a,p-1}; nu in R^2; Psi : R^2 -> B_{rho_1} differentiable as a map into W with D Psi(theta) nu = X_Lambda(Psi(theta)) + X_{bar G}(Psi(theta)) + X_{G^nor}(Psi(theta)) + X_K(Psi(theta)) in W_{a,p-1} for every theta; local data: w = Psi(theta)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:transport-tori-weak (all such nu, Psi; every theta); m > 0 fixed (standing assumption); within the step: theta
SOURCE_CONCLUSION: D Psi(theta) nu = X_{H'}(w) in W, D(Gamma o Psi)(theta) nu = D Gamma(w) X_{H'}(w) = X_H(Gamma(w)), Gamma(w) in W+, and the coefficient system as in Corollary bpW:w3:transport-tori; pointwise in theta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w3:wk-reg, bpW:w3:transport-tori, bpW:w3:flow, bpW:w3:main, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w3:wk-reg | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-transport@L860-L860 | w in B_{rho_1} cap W+
EDGE: bpW:w3:transport-tori | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-transport@L861-L861 | X_{H'} and the coefficient-system argument
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-transport@L862-L862 | Gamma is differentiable on W ((i))
EDGE: bpW:w3:main | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-transport@L863-L863 | (iv) conjugacy at w
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-transport@L859-L865 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W-w2+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:class-remark
KIND: claim
TITLE: Regularity class used by the W6 torus proof
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:class-remark@L771-L778
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:class-remark@L771-L778
CONTRACT_ID: bpW:w3:class-remark
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data: m > 0, a >= 0, p >= 1/2, J = {1,2}; the normal-form objects Gamma,K,X_K
SOURCE_QUANTIFIERS: on the complex ball B_{rho_1}, and on its real form as stated
SOURCE_CONCLUSION: Gamma,K,X_K are complex analytic on B_{rho_1}; Gamma and K arise from compositions of power series, X_{K_1} from composition and operator inversion, X_{K_2} from Yseries; their real restrictions are real analytic; analyticity implies holomorphy in the sense of W1, so W1 Cauchy estimates apply
CONSTANT_SCOPE: rho_1 and the preceding constants retain their W3 dependence on m,a,p; no new constant
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:flow, bpW:w3:main, bpW:w3:Yseries, bpW:w3:real-restrict, bpW:w1:holomorphic, bpW:w1:ext-analytic, bpW:w3#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:class-remark@L772-L773 | Gamma has its analytic power series
EDGE: bpW:w3:main | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:class-remark@L772-L774 | K and X_K are analytic
EDGE: bpW:w3:Yseries | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:class-remark@L774-L774 | the explicit series for X_{K_2}
EDGE: bpW:w3:real-restrict | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:class-remark@L774-L774 | real restrictions are analytic
EDGE: bpW:w1:holomorphic | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:class-remark@L776-L777 | the definition of holomorphy to which analyticity is applied
EDGE: bpW:w1:ext-analytic | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:class-remark@L776-L777 | analytic maps are Frechet differentiable, hence holomorphic in the cited definition
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:class-remark@L771-L778 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: new+sol-delta7-W-w3+sol-global-W
REVIEWER: sol-delta9-W-W-w3
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Restored because stepW:w6:t-an cites this fact at w6-iteration.tex L383 inside a proof. Source topology only; no Lean proof status inferred.

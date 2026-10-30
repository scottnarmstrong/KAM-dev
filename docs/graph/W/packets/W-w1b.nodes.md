NODE: bpW:w1:sine-completeness
KIND: lemma
TITLE: Completeness of the sine system
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-completeness@L593-L596
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-completeness@L598-L613
CONTRACT_ID: bpW:w1:sine-completeness
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (i) f in L^2(0,pi) with int_0^pi f phi_l = 0 for all l >= 1; (ii) moreover f continuous on [0,pi]
SOURCE_QUANTIFIERS: for all f
SOURCE_CONCLUSION: (i) f = 0 a.e. on (0,pi); (ii) f = 0 on [0,pi]
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#sineMode, stepW:w1:odd, stepW:w1:coeffs, stepW:w1:basis, stepW:w1:cont
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-completeness@L594-L594 | the sine modes phi_l
EDGE: stepW:w1:odd | blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-completeness@L599-L599 | proof step
EDGE: stepW:w1:coeffs | blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-completeness@L602-L602 | proof step
EDGE: stepW:w1:basis | blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-completeness@L606-L606 | proof step
EDGE: stepW:w1:cont | blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-completeness@L610-L610 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:odd
KIND: step
TITLE: Odd extension
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:odd@L599-L601
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:odd@L599-L601
CONTRACT_ID: stepW:w1:odd
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:sine-completeness: (i) f in L^2(0,pi) with int_0^pi f phi_l = 0 for all l >= 1; (ii) moreover f continuous on [0,pi]
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:sine-completeness (for all f); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the odd extension g of f to R/2piZ lies in L^2 with ¦¦g¦¦^2 = 2¦¦f¦¦^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:coeffs
KIND: step
TITLE: Fourier coefficients vanish
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:coeffs@L602-L605
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:coeffs@L602-L605
CONTRACT_ID: stepW:w1:coeffs
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:sine-completeness: (i) f in L^2(0,pi) with int_0^pi f phi_l = 0 for all l >= 1; (ii) moreover f continuous on [0,pi]; local data: the hypothesis of (i)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:sine-completeness (for all f); within the step: n in Z; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: int_{-pi}^{pi} g e^{-inx} = -2i int_0^pi f sin(nx) = 0 for all n
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:odd, bpW:w0:basis#sineMode
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:odd | blueprint-W/parts/w1-sequences.tex#stepW:w1:coeffs@L603-L603 | the odd extension g
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w1-sequences.tex#stepW:w1:coeffs@L605-L605 | sin(nx) = sqrt(pi/2) phi_n(x)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:basis
KIND: step
TITLE: Hilbert basis
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:basis@L606-L609
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:basis@L606-L609
CONTRACT_ID: stepW:w1:basis
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:sine-completeness: (i) f in L^2(0,pi) with int_0^pi f phi_l = 0 for all l >= 1; (ii) moreover f continuous on [0,pi]
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:sine-completeness (for all f); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the Fourier coefficients of g for the normalized Haar measure vanish, so g = 0 in L^2 and f = 0 a.e. on (0,pi)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:coeffs, bpW:w1:ext-fourier
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:coeffs | blueprint-W/parts/w1-sequences.tex#stepW:w1:basis@L607-L607 | the vanishing integrals
EDGE: bpW:w1:ext-fourier | blueprint-W/parts/w1-sequences.tex#stepW:w1:basis@L608-L608 | the characters form a Hilbert basis (injective coefficient map)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:cont
KIND: step
TITLE: Continuity
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:cont@L610-L612
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:cont@L610-L612
CONTRACT_ID: stepW:w1:cont
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:sine-completeness: (i) f in L^2(0,pi) with int_0^pi f phi_l = 0 for all l >= 1; (ii) moreover f continuous on [0,pi]
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:sine-completeness (for all f); within the step: x_0 in [0,pi]; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: f(x_0) != 0 would give ¦f¦ > ¦f(x_0)¦/2 on a subinterval of positive length, contradicting (i); so f = 0 on [0,pi]
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:basis
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:basis | blueprint-W/parts/w1-sequences.tex#stepW:w1:cont@L612-L612 | (i): f = 0 a.e.
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:sine-feature
KIND: lemma
TITLE: Analytic sine features
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-feature@L617-L629
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-feature@L631-L645
CONTRACT_ID: bpW:w1:sine-feature
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a > 0, p in R, k in N; beta : N_+ -> R with ¦beta_j¦ <= B j^nu for some B, nu >= 0; Psi(x)_j = beta_j phi_j^(k)(x)/omega_{a,p}(j), phi_j^(k)(x) = sqrt(2/pi) j^k sin^(k)(jx), for x in C with ¦Im x¦ < a
SOURCE_QUANTIFIERS: for all a > 0, p, k, beta, B, nu; (i) for 0 < a' < a; (iii) for real x, y in l^2_R
SOURCE_CONCLUSION: (i) with b_j = sqrt(2/pi) B j^{nu+k-p} e^{-(a-a')j}, ¦Psi(x)_j¦ <= b_j for ¦Im x¦ <= a' and sum b_j < infinity; (ii) Psi is holomorphic on {¦Im x¦ < a}, hence C-analytic there, real for real x, and Psi_R = re o Psi¦_R : R -> l^2_R is real analytic; (iii) <Psi_R(x),y> = sum_j beta_j (kappa_{a,p} y)_j phi_j^(k)(x), absolutely convergent
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#sineMode, bpW:w1:transport, stepW:w1:growth, stepW:w1:normal, stepW:w1:sinereal
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-feature@L620-L620 | the modes phi_j and their derivatives
EDGE: bpW:w1:transport | blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-feature@L620-L620 | the weights omega_{a,p} and kappa_{a,p}
EDGE: stepW:w1:growth | blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-feature@L632-L632 | proof step
EDGE: stepW:w1:normal | blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-feature@L636-L636 | proof step
EDGE: stepW:w1:sinereal | blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-feature@L641-L641 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:growth
KIND: step
TITLE: Growth on the strip
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:growth@L632-L635
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:growth@L632-L635
CONTRACT_ID: stepW:w1:growth
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:sine-feature: a > 0, p in R, k in N; beta : N_+ -> R with ¦beta_j¦ <= B j^nu for some B, nu >= 0; Psi(x)_j = beta_j phi_j^(k)(x)/omega_{a,p}(j), phi_j^(k)(x) = sqrt(2/pi) j^k sin^(k)(jx), for x in C with ¦Im x¦ < a; local data: ¦Im x¦ <= a' < a
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:sine-feature (for all a > 0, p, k, beta, B, nu; (i) for 0 < a' < a; (iii) for real x, y in l^2_R); within the step: j; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦sin^(k)(jx)¦ <= e^{j¦Im x¦}, so ¦Psi(x)_j¦ <= b_j, and sum b_j < infinity since a - a' > 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:normal
KIND: step
TITLE: Normal convergence
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:normal@L636-L640
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:normal@L636-L640
CONTRACT_ID: stepW:w1:normal
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:sine-feature: a > 0, p in R, k in N; beta : N_+ -> R with ¦beta_j¦ <= B j^nu for some B, nu >= 0; Psi(x)_j = beta_j phi_j^(k)(x)/omega_{a,p}(j), phi_j^(k)(x) = sqrt(2/pi) j^k sin^(k)(jx), for x in C with ¦Im x¦ < a
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:sine-feature (for all a > 0, p, k, beta, B, nu; (i) for 0 < a' < a; (iii) for real x, y in l^2_R); within the step: N; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the partial sums Psi^N are holomorphic and converge to Psi uniformly on ¦Im x¦ <= a', hence locally uniformly on the strip; Psi is holomorphic and analytic
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:growth, bpW:w1:ext-onevar
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:growth | blueprint-W/parts/w1-sequences.tex#stepW:w1:normal@L638-L638 | the tail bound sum_{j>N} b_j
EDGE: bpW:w1:ext-onevar | blueprint-W/parts/w1-sequences.tex#stepW:w1:normal@L640-L640 | locally uniform limits of holomorphic maps are holomorphic; holomorphic on open subsets of C implies analytic
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:sinereal
KIND: step
TITLE: Real restriction
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:sinereal@L641-L644
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:sinereal@L641-L644
CONTRACT_ID: stepW:w1:sinereal
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:sine-feature: a > 0, p in R, k in N; beta : N_+ -> R with ¦beta_j¦ <= B j^nu for some B, nu >= 0; Psi(x)_j = beta_j phi_j^(k)(x)/omega_{a,p}(j), phi_j^(k)(x) = sqrt(2/pi) j^k sin^(k)(jx), for x in C with ¦Im x¦ < a
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:sine-feature (for all a > 0, p, k, beta, B, nu; (i) for 0 < a' < a; (iii) for real x, y in l^2_R); within the step: real x, y; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Psi(x) = iota Psi_R(x) for real x and Psi_R = re o Psi o (R -> C) is real analytic; (iii) by lp.inner_eq_tsum and y_j/omega(j) = (kappa y)_j
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:complexification-lemma, bpW:w1:ext-lp, bpW:w1:transport
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:complexification-lemma | blueprint-W/parts/w1-sequences.tex#stepW:w1:sinereal@L643-L643 | (ii): R-analyticity of re o f o l
EDGE: bpW:w1:ext-lp | blueprint-W/parts/w1-sequences.tex#stepW:w1:sinereal@L643-L643 | the inner product of l^2 as a tsum
EDGE: bpW:w1:transport | blueprint-W/parts/w1-sequences.tex#stepW:w1:sinereal@L644-L644 | kappa_{a,p}
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:recon-analytic
KIND: corollary
TITLE: Analytic reconstruction
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:recon-analytic@L648-L670
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:recon-analytic@L672-L692
CONTRACT_ID: bpW:w1:recon-analytic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: k in N; Psi^{U,k}_R, Psi^{V,k}_R the real feature maps of Lemma bpW:w1:sine-feature with a = p = 1 and beta_j = lambda_j^{-1/2}, resp. lambda_j^{1/2}; U^(k)_y(x) = <Psi^{U,k}_R(x),y> = sum coeff y j/sqrt(lambda_j) phi_j^(k)(x), V^(k)_y(x) = sum sqrt(lambda_j) coeff y j phi_j^(k)(x) for y in l^2_R, x in R; (iii) S a real normed space and Y : S -> l^2_R real analytic at s_0
SOURCE_QUANTIFIERS: for all k, y, real x; (iii) for all S, Y, s_0, x_0
SOURCE_CONCLUSION: the series converge absolutely; (i) U^(0)_y(x) = reconU m hm y x and V^(0)_y(x) = reconV m hm y x; (ii) x -> U^(k)_y(x) has derivative U^(k+1)_y(x) (HasDerivAt), likewise V; U^(k)_y is the k-th derivative of reconU m hm y (iteratedDeriv k), and derivWithin (reconU m hm y) (Icc 0 pi) x = U^(1)_y(x) for x in [0,pi]; (iii) (s,x) -> U^(k)_{Y(s)}(x) and V^(k)_{Y(s)}(x) are real analytic on S x R at (s_0,x_0); in particular for S = R^n the iterated x-derivatives of reconU m hm (Y s) and reconV m hm (Y s) are real analytic
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:sine-feature, bpW:w0:basis#lam, bpW:w0:ellap#coeff, bpW:w0:reconstruction#reconU, bpW:w0:reconstruction#reconV, stepW:w1:bil, stepW:w1:recanalytic, stepW:w1:recder, bpW:w0:basis#sineMode
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:sine-feature | blueprint-W/parts/w1-sequences.tex#bpW:w1:recon-analytic@L650-L650 | the feature maps
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#bpW:w1:recon-analytic@L650-L650 | beta_j = lambda_j^{+-1/2}
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w1-sequences.tex#bpW:w1:recon-analytic@L652-L652 | coeff y j in the series
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w1-sequences.tex#bpW:w1:recon-analytic@L656-L656 | the frozen reconU in (i), (ii)
EDGE: bpW:w0:reconstruction#reconV | blueprint-W/parts/w1-sequences.tex#bpW:w1:recon-analytic@L656-L656 | the frozen reconV in (i)
EDGE: stepW:w1:bil | blueprint-W/parts/w1-sequences.tex#bpW:w1:recon-analytic@L673-L673 | proof step
EDGE: stepW:w1:recanalytic | blueprint-W/parts/w1-sequences.tex#bpW:w1:recon-analytic@L677-L677 | proof step
EDGE: stepW:w1:recder | blueprint-W/parts/w1-sequences.tex#bpW:w1:recon-analytic@L683-L683 | proof step
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w1-sequences.tex#bpW:w1:recon-analytic@L652-L652 | the sine modes phi_j occur directly here (frozen sineMode)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:bil
KIND: step
TITLE: Bilinear form
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:bil@L673-L676
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:bil@L673-L676
CONTRACT_ID: stepW:w1:bil
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:recon-analytic: k in N; Psi^{U,k}_R, Psi^{V,k}_R the real feature maps of Lemma bpW:w1:sine-feature with a = p = 1 and beta_j = lambda_j^{-1/2}, resp. lambda_j^{1/2}; U^(k)_y(x) = <Psi^{U,k}_R(x),y> = sum coeff y j/sqrt(lambda_j) phi_j^(k)(x), V^(k)_y(x) = sum sqrt(lambda_j) coeff y j phi_j^(k)(x) for y in l^2_R, x in R; (iii) S a real normed space and Y : S -> l^2_R real analytic at s_0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:recon-analytic (for all k, y, real x; (iii) for all S, Y, s_0, x_0); within the step: y, x; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦beta_j¦ <= (1+m)^{1/4} j^{1/2}, so Lemma bpW:w1:sine-feature applies; (iii) gives the series forms and absolute convergence; for k = 0 the series is the frozen tsum termwise, which is (i)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:sine-feature, bpW:w0:basis#lambda-facts, bpW:w0:ellap#coeff, bpW:w0:reconstruction#reconU, bpW:w0:reconstruction#reconV
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:sine-feature | blueprint-W/parts/w1-sequences.tex#stepW:w1:bil@L674-L674 | (iii) and its hypothesis ¦beta_j¦ <= B j^nu
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w1-sequences.tex#stepW:w1:bil@L674-L674 | lambda_j^{+-1/2} <= (1+m)^{1/4} j^{1/2}
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w1-sequences.tex#stepW:w1:bil@L675-L675 | coeff y j = (kappa_{1,1} y)_j
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w1-sequences.tex#stepW:w1:bil@L676-L676 | the frozen tsum of reconU
EDGE: bpW:w0:reconstruction#reconV | blueprint-W/parts/w1-sequences.tex#stepW:w1:bil@L676-L676 | the frozen tsum of reconV
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:recanalytic
KIND: step
TITLE: Analyticity
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:recanalytic@L677-L682
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:recanalytic@L677-L682
CONTRACT_ID: stepW:w1:recanalytic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:recon-analytic: k in N; Psi^{U,k}_R, Psi^{V,k}_R the real feature maps of Lemma bpW:w1:sine-feature with a = p = 1 and beta_j = lambda_j^{-1/2}, resp. lambda_j^{1/2}; U^(k)_y(x) = <Psi^{U,k}_R(x),y> = sum coeff y j/sqrt(lambda_j) phi_j^(k)(x), V^(k)_y(x) = sum sqrt(lambda_j) coeff y j phi_j^(k)(x) for y in l^2_R, x in R; (iii) S a real normed space and Y : S -> l^2_R real analytic at s_0; local data: Y analytic at s_0; Psi^{U,k}_R analytic
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:recon-analytic (for all k, y, real x; (iii) for all S, Y, s_0, x_0); within the step: (s_0,x_0); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the composite of the continuous bilinear inner product with the analytic pair (Psi^{U,k}_R(x), Y(s)) is analytic at (s_0,x_0); this is (iii)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:sine-feature, bpW:w1:ext-analytic
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:sine-feature | blueprint-W/parts/w1-sequences.tex#stepW:w1:recanalytic@L680-L680 | (ii): Psi_R is analytic
EDGE: bpW:w1:ext-analytic | blueprint-W/parts/w1-sequences.tex#stepW:w1:recanalytic@L679-L679 | bilinear maps, pairs and compositions of analytic maps are analytic
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:recder
KIND: step
TITLE: Derivatives
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:recder@L683-L691
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:recder@L683-L691
CONTRACT_ID: stepW:w1:recder
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:recon-analytic: k in N; Psi^{U,k}_R, Psi^{V,k}_R the real feature maps of Lemma bpW:w1:sine-feature with a = p = 1 and beta_j = lambda_j^{-1/2}, resp. lambda_j^{1/2}; U^(k)_y(x) = <Psi^{U,k}_R(x),y> = sum coeff y j/sqrt(lambda_j) phi_j^(k)(x), V^(k)_y(x) = sum sqrt(lambda_j) coeff y j phi_j^(k)(x) for y in l^2_R, x in R; (iii) S a real normed space and Y : S -> l^2_R real analytic at s_0; local data: Psi^{U,k}_R analytic
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:recon-analytic (for all k, y, real x; (iii) for all S, Y, s_0, x_0); within the step: k, y, x; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (Psi^{U,k}_R)' = Psi^{U,k+1}_R coordinatewise, so d/dx U^(k)_y = U^(k+1)_y; iterating from (i) gives the iterated derivatives of reconU m hm y; at x in [0,pi] the derivative within [0,pi] equals the two-sided derivative (uniqueDiffOn_Icc); the same for V; this is (ii)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:sine-feature, bpW:w1:ext-analytic, bpW:w1:space, stepW:w1:bil, bpW:w0:basis#sineMode, bpW:w0:reconstruction#reconU
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:sine-feature | blueprint-W/parts/w1-sequences.tex#stepW:w1:recder@L684-L684 | (ii): Psi_R analytic, hence differentiable
EDGE: bpW:w1:ext-analytic | blueprint-W/parts/w1-sequences.tex#stepW:w1:recder@L684-L684 | analytic maps are differentiable
EDGE: bpW:w1:space | blueprint-W/parts/w1-sequences.tex#stepW:w1:recder@L686-L686 | (ii): coordinate evaluation is continuous linear
EDGE: stepW:w1:bil | blueprint-W/parts/w1-sequences.tex#stepW:w1:recder@L689-L689 | (i): U^(0)_y = reconU m hm y
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w1-sequences.tex#stepW:w1:recder@L687-L687 | the sine modes phi_j occur directly here (frozen sineMode)
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w1-sequences.tex#stepW:w1:recder@L688-L688 | U_m occurs directly here (frozen reconU)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:complexification
KIND: definition
TITLE: Complexification
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:complexification@L698-L703
PROOF_SOURCE: -
CONTRACT_ID: bpW:w1:complexification
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: l^2_R, l^2_C and products
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: defines iota : l^2_R -> l^2_C, re : l^2_C -> l^2_R, conjugation, componentwise on products (E^C_{a,p} represented by (l^2_C)^2), and: f is real on reals if f(iota y) in iota(l^2_R) whenever defined
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:complexification-lemma
KIND: lemma
TITLE: Complexification and real analyticity
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:complexification-lemma@L707-L718
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:complexification-lemma@L720-L725
CONTRACT_ID: bpW:w1:complexification-lemma
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (ii) F_1, F_2 complex Banach, V real normed, l : V -> F_1 and pi : F_2 -> W continuous R-linear, f C-analytic at l(x); (iii) f defined near iota y, C-analytic at iota y and real on reals near iota y
SOURCE_QUANTIFIERS: for all such data
SOURCE_CONCLUSION: (i) iota, re are continuous R-linear, ¦¦iota y¦¦ = ¦¦y¦¦, ¦¦re z¦¦ <= ¦¦z¦¦, re o iota = id, ¦¦iota y + i iota y'¦¦^2 = ¦¦y¦¦^2 + ¦¦y'¦¦^2, conjugation is a conjugate-linear isometry, and all commute with tau, kappa and real multipliers; (ii) pi o f o l is R-analytic at x; (iii) g = re o f o iota is R-analytic at y, iota o g = f o iota near y, and Dg(y)h = re Df(iota y) iota h
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:complexification, bpW:w1:transport, bpW:w1:ext-analytic
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:complexification | blueprint-W/parts/w1-sequences.tex#bpW:w1:complexification-lemma@L709-L709 | iota, re, conjugation
EDGE: bpW:w1:transport | blueprint-W/parts/w1-sequences.tex#bpW:w1:complexification-lemma@L711-L711 | commutation with tau, kappa
EDGE: bpW:w1:ext-analytic | blueprint-W/parts/w1-sequences.tex#bpW:w1:complexification-lemma@L722-L722 | C-analytic is R-analytic; composition with continuous linear maps
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:holomorphic
KIND: definition
TITLE: Holomorphic maps on Banach domains
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:holomorphic@L728-L734
PROOF_SOURCE: -
CONTRACT_ID: bpW:w1:holomorphic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: F_1, F_2 complex Banach spaces, U subset F_1 open
SOURCE_QUANTIFIERS: f : U -> F_2
SOURCE_CONCLUSION: defines: f is holomorphic iff complex Frechet differentiable at every point of U (DifferentiableOn C f U); bounds are hypotheses ¦¦f(z)¦¦ <= M for z in U, never an unguarded supremum
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:cauchy
KIND: lemma
TITLE: Cauchy estimate
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:cauchy@L737-L742
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:cauchy@L744-L752
CONTRACT_ID: bpW:w1:cauchy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: r > 0, M >= 0, f holomorphic on B(v,r) subset F_1 with ¦¦f(z)¦¦ <= M there; for the consequences delta > 0, f holomorphic on open V with ¦¦f¦¦ <= M, B(w,delta) subset V, C convex with C + B(0,delta) subset V
SOURCE_QUANTIFIERS: for all such data
SOURCE_CONCLUSION: ¦¦Df(v)¦¦ <= M/r; ¦¦Df(w)¦¦ <= M/delta; f is (M/delta)-Lipschitz on C
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:holomorphic, stepW:w1:lines, stepW:w1:onevar, stepW:w1:margins
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:holomorphic | blueprint-W/parts/w1-sequences.tex#bpW:w1:cauchy@L738-L738 | holomorphic maps on Banach domains
EDGE: stepW:w1:lines | blueprint-W/parts/w1-sequences.tex#bpW:w1:cauchy@L745-L745 | proof step
EDGE: stepW:w1:onevar | blueprint-W/parts/w1-sequences.tex#bpW:w1:cauchy@L748-L748 | proof step
EDGE: stepW:w1:margins | blueprint-W/parts/w1-sequences.tex#bpW:w1:cauchy@L750-L750 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:lines
KIND: step
TITLE: Complex lines
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:lines@L745-L747
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:lines@L745-L747
CONTRACT_ID: stepW:w1:lines
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:cauchy: r > 0, M >= 0, f holomorphic on B(v,r) subset F_1 with ¦¦f(z)¦¦ <= M there; for the consequences delta > 0, f holomorphic on open V with ¦¦f¦¦ <= M, B(w,delta) subset V, C convex with C + B(0,delta) subset V; local data: u in F_1, ¦¦u¦¦ = 1, 0 < r' < r
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:cauchy (for all such data); within the step: u, r'; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: phi(zeta) = f(v + zeta u) is holomorphic on ¦zeta¦ < r', continuous on ¦zeta¦ <= r', phi'(0) = Df(v)u, ¦¦phi¦¦ <= M
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:onevar
KIND: step
TITLE: One-variable estimate
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:onevar@L748-L749
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:onevar@L748-L749
CONTRACT_ID: stepW:w1:onevar
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:cauchy: r > 0, M >= 0, f holomorphic on B(v,r) subset F_1 with ¦¦f(z)¦¦ <= M there; for the consequences delta > 0, f holomorphic on open V with ¦¦f¦¦ <= M, B(w,delta) subset V, C convex with C + B(0,delta) subset V
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:cauchy (for all such data); within the step: u; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦¦Df(v)u¦¦ <= M/r'; letting r' -> r and taking sup over u, ¦¦Df(v)¦¦ <= M/r
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:lines, bpW:w1:ext-onevar
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:lines | blueprint-W/parts/w1-sequences.tex#stepW:w1:onevar@L749-L749 | the one-variable function phi
EDGE: bpW:w1:ext-onevar | blueprint-W/parts/w1-sequences.tex#stepW:w1:onevar@L749-L749 | the Cauchy estimate in one variable
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:margins
KIND: step
TITLE: Margins
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:margins@L750-L751
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:margins@L750-L751
CONTRACT_ID: stepW:w1:margins
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:cauchy: r > 0, M >= 0, f holomorphic on B(v,r) subset F_1 with ¦¦f(z)¦¦ <= M there; for the consequences delta > 0, f holomorphic on open V with ¦¦f¦¦ <= M, B(w,delta) subset V, C convex with C + B(0,delta) subset V
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:cauchy (for all such data); within the step: w, C; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: apply on B(w,delta) for ¦¦Df(w)¦¦ <= M/delta; the Lipschitz bound on C by the mean value inequality
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:onevar, bpW:w1:ext-unifderiv
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:onevar | blueprint-W/parts/w1-sequences.tex#stepW:w1:margins@L751-L751 | the estimate on balls
EDGE: bpW:w1:ext-unifderiv | blueprint-W/parts/w1-sequences.tex#stepW:w1:margins@L751-L751 | the mean value inequality on convex sets
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:deriv-continuous
KIND: lemma
TITLE: Derivatives of holomorphic maps are continuous
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:deriv-continuous@L755-L760
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:deriv-continuous@L762-L775
CONTRACT_ID: bpW:w1:deriv-continuous
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U subset F_1 open, f : U -> F_2 holomorphic; w_0 in U, rho > 0, B >= 0 with B(w_0,2rho) subset U and ¦¦f¦¦ <= B on B(w_0,2rho)
SOURCE_QUANTIFIERS: for all such data; w, w' in B(w_0,rho/2)
SOURCE_CONCLUSION: ¦¦Df(w) - Df(w')¦¦ <= 2 B rho^{-2} ¦¦w - w'¦¦; such rho, B exist for every w_0, so Df : U -> L(F_1,F_2) is continuous (ContinuousOn (fderiv C f) U)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:holomorphic, stepW:w1:dcbound, stepW:w1:dcintegral, stepW:w1:dclip
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:holomorphic | blueprint-W/parts/w1-sequences.tex#bpW:w1:deriv-continuous@L756-L756 | holomorphic maps
EDGE: stepW:w1:dcbound | blueprint-W/parts/w1-sequences.tex#bpW:w1:deriv-continuous@L763-L763 | proof step
EDGE: stepW:w1:dcintegral | blueprint-W/parts/w1-sequences.tex#bpW:w1:deriv-continuous@L765-L765 | proof step
EDGE: stepW:w1:dclip | blueprint-W/parts/w1-sequences.tex#bpW:w1:deriv-continuous@L769-L769 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:dcbound
KIND: step
TITLE: Existence of $\rho$, $B$
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:dcbound@L763-L764
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:dcbound@L763-L764
CONTRACT_ID: stepW:w1:dcbound
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:deriv-continuous: U subset F_1 open, f : U -> F_2 holomorphic; w_0 in U, rho > 0, B >= 0 with B(w_0,2rho) subset U and ¦¦f¦¦ <= B on B(w_0,2rho); local data: f continuous at w_0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:deriv-continuous (for all such data; w, w' in B(w_0,rho/2)); within the step: w_0; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦¦f(z)¦¦ <= ¦¦f(w_0)¦¦ + 1 =: B on some ball B(w_0,2rho) subset U
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:dcintegral
KIND: step
TITLE: Cauchy integral along lines
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:dcintegral@L765-L768
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:dcintegral@L765-L768
CONTRACT_ID: stepW:w1:dcintegral
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:deriv-continuous: U subset F_1 open, f : U -> F_2 holomorphic; w_0 in U, rho > 0, B >= 0 with B(w_0,2rho) subset U and ¦¦f¦¦ <= B on B(w_0,2rho); local data: w in B(w_0,rho/2), ¦¦u¦¦ = 1
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:deriv-continuous (for all such data; w, w' in B(w_0,rho/2)); within the step: w, u; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: phi(zeta) = f(w + zeta u) is holomorphic for ¦zeta¦ < 3rho/2 and Df(w)u = (1/(2 pi i)) oint_{¦zeta¦=rho/2} f(w + zeta u) zeta^{-2} dzeta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-onevar
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-onevar | blueprint-W/parts/w1-sequences.tex#stepW:w1:dcintegral@L767-L767 | the Cauchy integral formula for phi'(0)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:dclip
KIND: step
TITLE: Lipschitz difference
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:dclip@L769-L774
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:dclip@L769-L774
CONTRACT_ID: stepW:w1:dclip
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:deriv-continuous: U subset F_1 open, f : U -> F_2 holomorphic; w_0 in U, rho > 0, B >= 0 with B(w_0,2rho) subset U and ¦¦f¦¦ <= B on B(w_0,2rho)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:deriv-continuous (for all such data; w, w' in B(w_0,rho/2)); within the step: w, w', u; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦¦Df¦¦ <= B/rho on B(w_0,rho), so the integrands differ by at most (B/rho)¦¦w - w'¦¦; subtracting the Cauchy integrals gives ¦¦(Df(w) - Df(w'))u¦¦ <= 2 B rho^{-2} ¦¦w - w'¦¦; sup over u
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:cauchy, stepW:w1:dcintegral, stepW:w1:dcbound
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:cauchy | blueprint-W/parts/w1-sequences.tex#stepW:w1:dclip@L771-L771 | margin rho inside B(w_0,2rho)
EDGE: stepW:w1:dcintegral | blueprint-W/parts/w1-sequences.tex#stepW:w1:dclip@L772-L772 | the two Cauchy integrals
EDGE: stepW:w1:dcbound | blueprint-W/parts/w1-sequences.tex#stepW:w1:dclip@L771-L771 | the bound B on B(w_0,2rho)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:uniform-limit
KIND: lemma
TITLE: Uniform limits
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:uniform-limit@L778-L786
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:uniform-limit@L788-L798
CONTRACT_ID: bpW:w1:uniform-limit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U subset F_1 open, f_k : U -> F_2 holomorphic, f_k -> f uniformly on U; (ii) moreover M >= 0 with ¦¦f(z)¦¦ <= M on U
SOURCE_QUANTIFIERS: for all such data; (i) balls B(w,delta), delta > 0, B(w,2delta) subset U; (ii) delta > 0 with B(w,delta) subset U
SOURCE_CONCLUSION: (i) f is holomorphic on U and Df_k -> Df uniformly on every such B(w,delta); if every f_k is real on reals, so is f; no boundedness of f assumed; (ii) ¦¦Df(w)¦¦ <= M/delta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:holomorphic, bpW:w1:complexification, stepW:w1:ulcauchy, stepW:w1:ullimit
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:holomorphic | blueprint-W/parts/w1-sequences.tex#bpW:w1:uniform-limit@L779-L779 | holomorphic maps
EDGE: bpW:w1:complexification | blueprint-W/parts/w1-sequences.tex#bpW:w1:uniform-limit@L782-L782 | real on reals
EDGE: stepW:w1:ulcauchy | blueprint-W/parts/w1-sequences.tex#bpW:w1:uniform-limit@L789-L789 | proof step
EDGE: stepW:w1:ullimit | blueprint-W/parts/w1-sequences.tex#bpW:w1:uniform-limit@L794-L794 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:ulcauchy
KIND: step
TITLE: Cauchy in derivatives
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:ulcauchy@L789-L793
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:ulcauchy@L789-L793
CONTRACT_ID: stepW:w1:ulcauchy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:uniform-limit: U subset F_1 open, f_k : U -> F_2 holomorphic, f_k -> f uniformly on U; (ii) moreover M >= 0 with ¦¦f(z)¦¦ <= M on U; local data: eps > 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:uniform-limit (for all such data; (i) balls B(w,delta), delta > 0, B(w,2delta) subset U; (ii) delta > 0 with B(w,delta) subset U); within the step: w' in B(w,delta); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (Df_k) is uniformly Cauchy on B(w,delta) in the complete space of bounded C-linear maps, with a uniform limit g
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:cauchy
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:cauchy | blueprint-W/parts/w1-sequences.tex#stepW:w1:ulcauchy@L791-L791 | applied to f_k - f_l with bound eps
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:ullimit
KIND: step
TITLE: Limit
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:ullimit@L794-L797
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:ullimit@L794-L797
CONTRACT_ID: stepW:w1:ullimit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:uniform-limit: U subset F_1 open, f_k : U -> F_2 holomorphic, f_k -> f uniformly on U; (ii) moreover M >= 0 with ¦¦f(z)¦¦ <= M on U
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:uniform-limit (for all such data; (i) balls B(w,delta), delta > 0, B(w,2delta) subset U; (ii) delta > 0 with B(w,delta) subset U); within the step: w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: f is C-differentiable on the ball with Df = g, hence holomorphic on U; real on reals since iota(l^2_R) is closed; (ii) is the Cauchy estimate for f
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:ulcauchy, bpW:w1:ext-unifderiv, bpW:w1:cauchy
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:ulcauchy | blueprint-W/parts/w1-sequences.tex#stepW:w1:ullimit@L795-L795 | the uniform limit g of Df_k
EDGE: bpW:w1:ext-unifderiv | blueprint-W/parts/w1-sequences.tex#stepW:w1:ullimit@L795-L795 | uniform limits of derivatives
EDGE: bpW:w1:cauchy | blueprint-W/parts/w1-sequences.tex#stepW:w1:ullimit@L797-L797 | (ii) applied to f itself
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:holo-analytic-fd
KIND: lemma
TITLE: Holomorphic maps of finitely many variables are analytic
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:holo-analytic-fd@L801-L811
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:holo-analytic-fd@L813-L836
CONTRACT_ID: bpW:w1:holo-analytic-fd
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U subset C^n open (max norm), F complex Banach, f : U -> F holomorphic; for the quantitative part n >= 1, r > 0 with bar P(z_0,r) subset U; for the real part F = E^C_{a,p} and f real on reals at the real points of U
SOURCE_QUANTIFIERS: for all such data
SOURCE_CONCLUSION: f is C-analytic on U (AnalyticOnNhd C f U; n = 0 trivial); there are r_1 > r and M_1 >= 0 with bar P(z_0,r_1) subset U, ¦¦f¦¦ <= M_1 there, and f = sum_alpha c_alpha (z - z_0)^alpha absolutely on P(z_0,r_1) with ¦¦c_alpha¦¦ <= M_1 r_1^{-¦alpha¦}; grouped by degree a FormalMultilinearSeries (p_m) with ¦¦p_m¦¦ <= binom(m+n-1,n-1) M_1 r_1^{-m} and HasFPowerSeriesOnBall f p z_0 r_1; re o f¦_{U cap R^n} is real analytic into E_{a,p}
CONSTANT_SCOPE: r_1, M_1 depend on f, z_0, r
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:holomorphic, bpW:w1:complexification, stepW:w1:hamargin, stepW:w1:hacoef, stepW:w1:hagroup, stepW:w1:hareal
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:holomorphic | blueprint-W/parts/w1-sequences.tex#bpW:w1:holo-analytic-fd@L802-L802 | holomorphic maps
EDGE: bpW:w1:complexification | blueprint-W/parts/w1-sequences.tex#bpW:w1:holo-analytic-fd@L809-L809 | real on reals
EDGE: stepW:w1:hamargin | blueprint-W/parts/w1-sequences.tex#bpW:w1:holo-analytic-fd@L814-L814 | proof step
EDGE: stepW:w1:hacoef | blueprint-W/parts/w1-sequences.tex#bpW:w1:holo-analytic-fd@L817-L817 | proof step
EDGE: stepW:w1:hagroup | blueprint-W/parts/w1-sequences.tex#bpW:w1:holo-analytic-fd@L824-L824 | proof step
EDGE: stepW:w1:hareal | blueprint-W/parts/w1-sequences.tex#bpW:w1:holo-analytic-fd@L834-L834 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:hamargin
KIND: step
TITLE: Margin
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hamargin@L814-L816
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hamargin@L814-L816
CONTRACT_ID: stepW:w1:hamargin
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:holo-analytic-fd: U subset C^n open (max norm), F complex Banach, f : U -> F holomorphic; for the quantitative part n >= 1, r > 0 with bar P(z_0,r) subset U; for the real part F = E^C_{a,p} and f real on reals at the real points of U; local data: bar P(z_0,r) subset U compact, U open
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:holo-analytic-fd (for all such data); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: bar P(z_0,r_1) subset U for some r_1 > r, and f is bounded by some M_1 on the compact bar P(z_0,r_1)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:hacoef
KIND: step
TITLE: Coefficients
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hacoef@L817-L823
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hacoef@L817-L823
CONTRACT_ID: stepW:w1:hacoef
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:holo-analytic-fd: U subset C^n open (max norm), F complex Banach, f : U -> F holomorphic; for the quantitative part n >= 1, r > 0 with bar P(z_0,r) subset U; for the real part F = E^C_{a,p} and f real on reals at the real points of U; local data: F complete
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:holo-analytic-fd (for all such data); within the step: alpha in N^n; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: there are c_alpha in F with ¦¦c_alpha¦¦ <= M_1 r_1^{-¦alpha¦} and f(z) = sum_alpha c_alpha (z - z_0)^alpha absolutely on P(z_0,r_1)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:hamargin, K:bp:p1:holomorphic-analytic, bpW:w1:ext-onevar, bpW:w1:ext-integral
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:hamargin | blueprint-W/parts/w1-sequences.tex#stepW:w1:hacoef@L819-L819 | the radius r_1 and the bound M_1
EDGE: K:bp:p1:holomorphic-analytic | blueprint-W/parts/w1-sequences.tex#stepW:w1:hacoef@L818-L818 | K's Cauchy-coefficient argument (steps han-cauchy..han-bounds), applied with W replaced by the complete F
EDGE: bpW:w1:ext-onevar | blueprint-W/parts/w1-sequences.tex#stepW:w1:hacoef@L821-L821 | the one-variable Cauchy formula for complete F
EDGE: bpW:w1:ext-integral | blueprint-W/parts/w1-sequences.tex#stepW:w1:hacoef@L823-L823 | Fubini and termwise integration of Bochner integrals on the torus
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Uses the proof of track K's Lemma bp:p1:holomorphic-analytic (steps han-cauchy to han-bounds) with radius r_1 and K's target W replaced by the complete space F (a carrier change); the text justifies the transfer (L821-L823: only the one-variable Cauchy formula for complete F and Bochner integration on the domain torus are used). Reviewer: check that the import and the two externals cover the transfer.

NODE: stepW:w1:hagroup
KIND: step
TITLE: Degree grouping
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hagroup@L824-L833
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hagroup@L824-L833
CONTRACT_ID: stepW:w1:hagroup
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:holo-analytic-fd: U subset C^n open (max norm), F complex Banach, f : U -> F holomorphic; for the quantitative part n >= 1, r > 0 with bar P(z_0,r) subset U; for the real part F = E^C_{a,p} and f real on reals at the real points of U
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:holo-analytic-fd (for all such data); within the step: m >= 0; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: p_m(h_1..h_m) = sum_{¦alpha¦=m} (prod (h_l)_{iota_alpha(l)}) c_alpha is a continuous m-linear map with ¦¦p_m¦¦ <= binom(m+n-1,n-1) M_1 r_1^{-m}; sum ¦¦p_m¦¦ rho^m < infinity for rho < r_1; regrouping gives HasFPowerSeriesOnBall f p z_0 r_1; f is analytic at every point of U
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:hacoef, bpW:w3:ext-tsum, bpW:w1:ext-analytic
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:hacoef | blueprint-W/parts/w1-sequences.tex#stepW:w1:hagroup@L829-L829 | the coefficients c_alpha and their bounds
EDGE: bpW:w3:ext-tsum | blueprint-W/parts/w1-sequences.tex#stepW:w1:hagroup@L831-L831 | regrouping an absolutely convergent multi-index series by degree
EDGE: bpW:w1:ext-analytic | blueprint-W/parts/w1-sequences.tex#stepW:w1:hagroup@L832-L832 | a power series with positive radius gives analyticity (HasFPowerSeriesOnBall)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:hareal
KIND: step
TITLE: Real points
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hareal@L834-L835
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hareal@L834-L835
CONTRACT_ID: stepW:w1:hareal
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:holo-analytic-fd: U subset C^n open (max norm), F complex Banach, f : U -> F holomorphic; for the quantitative part n >= 1, r > 0 with bar P(z_0,r) subset U; for the real part F = E^C_{a,p} and f real on reals at the real points of U; local data: F = E^C_{a,p}, f real on reals
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:holo-analytic-fd (for all such data); within the step: real points; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: re o f¦_{U cap R^n} is real analytic
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:complexification-lemma
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:complexification-lemma | blueprint-W/parts/w1-sequences.tex#stepW:w1:hareal@L835-L835 | (iii)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:torus-analytic
KIND: corollary
TITLE: Real-analytic tori from complex strips
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:torus-analytic@L839-L844
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:torus-analytic@L846-L849
CONTRACT_ID: bpW:w1:torus-analytic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: s > 0, T_s = {theta in C^2 : max_i ¦Im theta_i¦ < s}; tilde K : T_s -> E^C_{1,1} holomorphic, real on reals, 1-periodic
SOURCE_QUANTIFIERS: for all such s, tilde K
SOURCE_CONCLUSION: K = re o tilde K¦_{R^2} : R^2 -> WaveSpace satisfies AnalyticOnNhd R K univ, is Z^2-periodic, and fderiv R K theta h = re D tilde K(theta) h for h in R^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:holo-analytic-fd, bpW:w1:complexification-lemma, bpW:w0:ellap#WaveSpace
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:holo-analytic-fd | blueprint-W/parts/w1-sequences.tex#bpW:w1:torus-analytic@L847-L847 | with U = T_s
EDGE: bpW:w1:complexification-lemma | blueprint-W/parts/w1-sequences.tex#bpW:w1:torus-analytic@L847-L847 | (iii): real restriction and its derivative
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w1-sequences.tex#bpW:w1:torus-analytic@L841-L841 | K takes values in WaveSpace (E_{1,1})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:flow
KIND: lemma
TITLE: Holomorphic flows
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:flow@L852-L866
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:flow@L868-L902
CONTRACT_ID: bpW:w1:flow
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: F complex Banach, V subset F open, X : V -> F holomorphic with ¦¦X(z)¦¦ <= M on V; U subset V open with B(w,2delta) subset V for all w in U; 0 < M < delta; L = M/delta < 1; (iii) F = E^C and X real on reals; (iv) X(.,xi), xi in Pi, each satisfying the hypotheses with the same V, U, M, delta, and N >= 0 with ¦¦X(z,xi) - X(z,zeta)¦¦ <= N on V
SOURCE_QUANTIFIERS: for all such data; w in U, t in [-1,1]
SOURCE_CONCLUSION: (i) a unique C^1 curve t -> phi^t(w), t in [-1,1], phi^0(w) = w, d/dt phi^t = X(phi^t), values in V, with ¦¦phi^t(w) - w¦¦ <= ¦t¦M <= M; (ii) w -> phi^t(w) is holomorphic on U with ¦¦D phi^t(w)¦¦ <= e^{L¦t¦}; (iii) phi^t is real on reals; (iv) ¦¦phi^t(w,xi) - phi^t(w,zeta)¦¦ <= ¦t¦ e^{L¦t¦} N
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:holomorphic, bpW:w1:complexification, stepW:w1:flowlip, stepW:w1:picard, stepW:w1:picardholo, stepW:w1:flowlim, stepW:w1:flowreal, stepW:w1:flowpar, bpW:w0:basis#sineMode
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:holomorphic | blueprint-W/parts/w1-sequences.tex#bpW:w1:flow@L853-L853 | holomorphic fields
EDGE: bpW:w1:complexification | blueprint-W/parts/w1-sequences.tex#bpW:w1:flow@L861-L861 | real on reals
EDGE: stepW:w1:flowlip | blueprint-W/parts/w1-sequences.tex#bpW:w1:flow@L869-L869 | proof step
EDGE: stepW:w1:picard | blueprint-W/parts/w1-sequences.tex#bpW:w1:flow@L872-L872 | proof step
EDGE: stepW:w1:picardholo | blueprint-W/parts/w1-sequences.tex#bpW:w1:flow@L876-L876 | proof step
EDGE: stepW:w1:flowlim | blueprint-W/parts/w1-sequences.tex#bpW:w1:flow@L889-L889 | proof step
EDGE: stepW:w1:flowreal | blueprint-W/parts/w1-sequences.tex#bpW:w1:flow@L895-L895 | proof step
EDGE: stepW:w1:flowpar | blueprint-W/parts/w1-sequences.tex#bpW:w1:flow@L897-L897 | proof step
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w1-sequences.tex#bpW:w1:flow@L857-L857 | the sine modes phi_j occur directly here (frozen sineMode)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:flowlip
KIND: step
TITLE: Lipschitz region
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlip@L869-L871
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlip@L869-L871
CONTRACT_ID: stepW:w1:flowlip
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:flow: F complex Banach, V subset F open, X : V -> F holomorphic with ¦¦X(z)¦¦ <= M on V; U subset V open with B(w,2delta) subset V for all w in U; 0 < M < delta; L = M/delta < 1; (iii) F = E^C and X real on reals; (iv) X(.,xi), xi in Pi, each satisfying the hypotheses with the same V, U, M, delta, and N >= 0 with ¦¦X(z,xi) - X(z,zeta)¦¦ <= N on V; local data: w in U, w' in B(w,delta)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:flow (for all such data; w in U, t in [-1,1]); within the step: w, w'; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦¦DX(w')¦¦ <= L and X is L-Lipschitz on the convex ball B(w,delta)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:cauchy
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:cauchy | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlip@L871-L871 | margin delta inside B(w,2delta) subset V
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:picard
KIND: step
TITLE: Picard iterates
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:picard@L872-L875
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:picard@L872-L875
CONTRACT_ID: stepW:w1:picard
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:flow: F complex Banach, V subset F open, X : V -> F holomorphic with ¦¦X(z)¦¦ <= M on V; U subset V open with B(w,2delta) subset V for all w in U; 0 < M < delta; L = M/delta < 1; (iii) F = E^C and X real on reals; (iv) X(.,xi), xi in Pi, each satisfying the hypotheses with the same V, U, M, delta, and N >= 0 with ¦¦X(z,xi) - X(z,zeta)¦¦ <= N on V
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:flow (for all such data; w in U, t in [-1,1]); within the step: k, w, t; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the Picard iterates phi_k stay in B(w,delta) (¦¦phi_k - w¦¦ <= ¦t¦M < delta), are continuous in (w,t), and ¦¦phi_{k+1} - phi_k¦¦ <= M L^k ¦t¦^{k+1}/(k+1)! uniformly in w
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:flowlip, bpW:w1:ext-integral, bpW:w0:basis#sineMode
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:flowlip | blueprint-W/parts/w1-sequences.tex#stepW:w1:picard@L875-L875 | L-Lipschitz on B(w,delta)
EDGE: bpW:w1:ext-integral | blueprint-W/parts/w1-sequences.tex#stepW:w1:picard@L873-L873 | the integral equation (Bochner integral)
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w1-sequences.tex#stepW:w1:picard@L873-L873 | the sine modes phi_j occur directly here (frozen sineMode)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:picardholo
KIND: step
TITLE: Holomorphy of the iterates
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:picardholo@L876-L888
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:picardholo@L876-L888
CONTRACT_ID: stepW:w1:picardholo
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:flow: F complex Banach, V subset F open, X : V -> F holomorphic with ¦¦X(z)¦¦ <= M on V; U subset V open with B(w,2delta) subset V for all w in U; 0 < M < delta; L = M/delta < 1; (iii) F = E^C and X real on reals; (iv) X(.,xi), xi in Pi, each satisfying the hypotheses with the same V, U, M, delta, and N >= 0 with ¦¦X(z,xi) - X(z,zeta)¦¦ <= N on V
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:flow (for all such data; w in U, t in [-1,1]); within the step: k; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: by induction w -> phi_k(w,t) is holomorphic on U, ¦¦D_w phi_k¦¦ <= sum_{i<=k} (L¦t¦)^i/i! <= e^{L¦t¦}, t -> D_w phi_k continuous; differentiation under the integral with domination L e^L
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:deriv-continuous, bpW:w1:ext-integral, stepW:w1:flowlip, stepW:w1:picard, bpW:w0:basis#sineMode
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:deriv-continuous | blueprint-W/parts/w1-sequences.tex#stepW:w1:picardholo@L881-L881 | DX is continuous on V
EDGE: bpW:w1:ext-integral | blueprint-W/parts/w1-sequences.tex#stepW:w1:picardholo@L883-L883 | differentiation under the integral (hasFDerivAt_integral_of_dominated_of_fderiv_le)
EDGE: stepW:w1:flowlip | blueprint-W/parts/w1-sequences.tex#stepW:w1:picardholo@L884-L884 | ¦¦DX¦¦ <= L on B(w,delta)
EDGE: stepW:w1:picard | blueprint-W/parts/w1-sequences.tex#stepW:w1:picardholo@L879-L879 | the iterates and their continuity
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w1-sequences.tex#stepW:w1:picardholo@L877-L877 | the sine modes phi_j occur directly here (frozen sineMode)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:flowlim
KIND: step
TITLE: Limit
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlim@L889-L894
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlim@L889-L894
CONTRACT_ID: stepW:w1:flowlim
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:flow: F complex Banach, V subset F open, X : V -> F holomorphic with ¦¦X(z)¦¦ <= M on V; U subset V open with B(w,2delta) subset V for all w in U; 0 < M < delta; L = M/delta < 1; (iii) F = E^C and X real on reals; (iv) X(.,xi), xi in Pi, each satisfying the hypotheses with the same V, U, M, delta, and N >= 0 with ¦¦X(z,xi) - X(z,zeta)¦¦ <= N on V
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:flow (for all such data; w in U, t in [-1,1]); within the step: w, t; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the iterates converge uniformly to phi, a C^1 solution of the integral equation; uniqueness among solutions in V; phi^t holomorphic with the derivative bound; this proves (i), (ii)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:picard, bpW:w1:ext-ode, bpW:w1:uniform-limit, stepW:w1:picardholo, bpW:w0:basis#sineMode
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:picard | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlim@L890-L890 | geometric convergence of the iterates
EDGE: bpW:w1:ext-ode | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlim@L891-L891 | uniqueness of ODE solutions for Lipschitz fields
EDGE: bpW:w1:uniform-limit | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlim@L893-L893 | holomorphy of the uniform limit
EDGE: stepW:w1:picardholo | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlim@L893-L893 | holomorphy and bounds of the iterates
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlim@L893-L893 | the sine modes phi_j occur directly here (frozen sineMode)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:flowreal
KIND: step
TITLE: Reality
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:flowreal@L895-L896
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:flowreal@L895-L896
CONTRACT_ID: stepW:w1:flowreal
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:flow: F complex Banach, V subset F open, X : V -> F holomorphic with ¦¦X(z)¦¦ <= M on V; U subset V open with B(w,2delta) subset V for all w in U; 0 < M < delta; L = M/delta < 1; (iii) F = E^C and X real on reals; (iv) X(.,xi), xi in Pi, each satisfying the hypotheses with the same V, U, M, delta, and N >= 0 with ¦¦X(z,xi) - X(z,zeta)¦¦ <= N on V
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:flow (for all such data; w in U, t in [-1,1]); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: every Picard iterate of a real point is real and the real subspace is closed, so phi^t is real on reals
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:picard, stepW:w1:flowlim
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:picard | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowreal@L896-L896 | the Picard iterates
EDGE: stepW:w1:flowlim | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowreal@L896-L896 | phi is their limit
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:flowpar
KIND: step
TITLE: Parameters
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:flowpar@L897-L901
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:flowpar@L897-L901
CONTRACT_ID: stepW:w1:flowpar
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:flow: F complex Banach, V subset F open, X : V -> F holomorphic with ¦¦X(z)¦¦ <= M on V; U subset V open with B(w,2delta) subset V for all w in U; 0 < M < delta; L = M/delta < 1; (iii) F = E^C and X real on reals; (iv) X(.,xi), xi in Pi, each satisfying the hypotheses with the same V, U, M, delta, and N >= 0 with ¦¦X(z,xi) - X(z,zeta)¦¦ <= N on V
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:flow (for all such data; w in U, t in [-1,1]); within the step: w, t; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: psi^t = phi^t(w,xi) - phi^t(w,zeta) satisfies ¦¦dpsi/dt¦¦ <= N + L¦¦psi¦¦, psi^0 = 0, so ¦¦psi^t¦¦ <= N(e^{L¦t¦} - 1)/L <= ¦t¦ e^{L¦t¦} N (both curves stay in the convex ball B(w,delta))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:flowlip, stepW:w1:flowlim, bpW:w1:ext-ode, bpW:w0:basis#sineMode
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:flowlip | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowpar@L899-L899 | X(.,zeta) is L-Lipschitz on B(w,delta)
EDGE: stepW:w1:flowlim | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowpar@L898-L898 | both trajectories lie in B(w,delta) by (i)
EDGE: bpW:w1:ext-ode | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowpar@L900-L900 | Gronwall's inequality
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowpar@L898-L898 | the sine modes phi_j occur directly here (frozen sineMode)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:kam-space
KIND: definition
TITLE: KAM phase space, domains, norms
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:kam-space@L916-L928
PROOF_SOURCE: -
CONTRACT_ID: bpW:w1:kam-space
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: a >= 0, p in R, bar p; s, r > 0
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: defines P^{a,p}_C = C^2 x C^2 x l^{a,p}_C x l^{a,p}_C (points (theta,y,u,v), weighted coordinates, max norm on C^2), D(s,r) = {max ¦Im theta_i¦ < s, ¦y¦ < r^2, ¦¦u¦¦_{a,p} + ¦¦v¦¦_{a,p} < r}, ¦W¦_{bar p,r} = ¦Theta¦ + ¦Y¦/r^2 + ¦¦U¦¦_{a,bar p}/r + ¦¦V¦¦_{a,bar p}/r, the operator norm ¦L¦_{r,s}, and period one: x = 2 pi theta is P96-K's angle, a strip ¦Im x¦ < s_K is ¦Im theta¦ < s_K/(2pi), theta-components are (2pi)^{-1} times x-components
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:transport
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:transport | blueprint-W/parts/w1-sequences.tex#bpW:w1:kam-space@L918-L918 | weighted coordinates of l^{a,p}_C
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:kam-domain
KIND: lemma
TITLE: Domains
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:kam-domain@L939-L943
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:kam-domain@L945-L951
CONTRACT_ID: bpW:w1:kam-domain
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0 < sigma <= 1, 0 < 2sigma < s, r > 0
SOURCE_QUANTIFIERS: for all such sigma, s, r; W_0, W
SOURCE_CONCLUSION: D(s,r) is open and convex; D(s',r') subset D(s,r) for s' <= s, r' <= r; every W_0 in D(s-2sigma,r/2) has W_0 + W in D(s-sigma,r) whenever ¦W¦_{p,r} < sigma/2; ¦W¦_{bar p,r} <= ¦W¦_{p,r} for bar p <= p and ¦W¦_{p,r} <= ¦W¦_{p,r'} for r' <= r
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:kam-space, bpW:w1:embed
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:kam-space | blueprint-W/parts/w1-sequences.tex#bpW:w1:kam-domain@L940-L940 | D(s,r) and the norms
EDGE: bpW:w1:embed | blueprint-W/parts/w1-sequences.tex#bpW:w1:kam-domain@L950-L950 | (i): norm comparison for bar p <= p
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:fourier-l2
KIND: lemma
TITLE: Hilbert-valued Fourier series on strips
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-l2@L955-L966
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-l2@L968-L990
CONTRACT_ID: bpW:w1:fourier-l2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: H complex Hilbert space, n >= 1, s > 0, T_s = {max ¦Im theta_i¦ < s}, u : T_s -> H holomorphic, 1-periodic, ¦¦u¦¦ <= M on T_s (M >= 0); hat u_k = int_{[0,1]^n} u(x) e^{-2 pi i k.x} dx; (ii) c_k in H with sum ¦¦c_k¦¦ e^{2pi¦k¦_1 s} < infinity
SOURCE_QUANTIFIERS: for all such data
SOURCE_CONCLUSION: (i) sum_k ¦¦hat u_k¦¦^2 e^{4 pi ¦k¦_1 s} <= 2^n M^2; (ii) v(theta) = sum c_k e^{2 pi i k.theta} converges absolutely and uniformly on T_s, is holomorphic and 1-periodic, hat v_k = c_k, ¦¦v¦¦ <= sum ¦¦c_k¦¦ e^{2pi¦k¦_1 s}; (iii) u is the sum of its Fourier series on T_{s'} for s' < s
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:holomorphic, stepW:w1:shift, stepW:w1:parseval, stepW:w1:orthants, stepW:w1:fsum
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:holomorphic | blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-l2@L957-L957 | holomorphic maps
EDGE: stepW:w1:shift | blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-l2@L969-L969 | proof step
EDGE: stepW:w1:parseval | blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-l2@L975-L975 | proof step
EDGE: stepW:w1:orthants | blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-l2@L980-L980 | proof step
EDGE: stepW:w1:fsum | blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-l2@L984-L984 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:shift
KIND: step
TITLE: Shifted coefficients
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:shift@L969-L974
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:shift@L969-L974
CONTRACT_ID: stepW:w1:shift
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:fourier-l2: H complex Hilbert space, n >= 1, s > 0, T_s = {max ¦Im theta_i¦ < s}, u : T_s -> H holomorphic, 1-periodic, ¦¦u¦¦ <= M on T_s (M >= 0); hat u_k = int_{[0,1]^n} u(x) e^{-2 pi i k.x} dx; (ii) c_k in H with sum ¦¦c_k¦¦ e^{2pi¦k¦_1 s} < infinity; local data: eta in R^n, max ¦eta_i¦ < s
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:fourier-l2 (for all such data); within the step: k; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: hat u_k e^{-2 pi k.eta} is the k-th Fourier coefficient of the continuous periodic x -> u(x + i eta)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:step:p1:dec-shift, bpW:w1:ext-lp
ROUTES: -
ROUTE_FOR: -
EDGE: K:step:p1:dec-shift | blueprint-W/parts/w1-sequences.tex#stepW:w1:shift@L973-L973 | the contour shift (cited as fourier-basic) applied to the scalar holomorphic functions <e,u>
EDGE: bpW:w1:ext-lp | blueprint-W/parts/w1-sequences.tex#stepW:w1:shift@L974-L974 | vectors of H are determined by the functionals <e,.>
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The text cites "the contour shift of track K's bp:p1:fourier-basic" (L973); fourier-basic contains no contour shift. The shift is K's step:p1:dec-shift (in the proof of bp:p1:decay), used here with an arbitrary shift eta instead of K's t_j = -rho' sgn(k_j). Suspected blueprint misreference (reported).

NODE: stepW:w1:parseval
KIND: step
TITLE: Parseval
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:parseval@L975-L979
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:parseval@L975-L979
CONTRACT_ID: stepW:w1:parseval
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:fourier-l2: H complex Hilbert space, n >= 1, s > 0, T_s = {max ¦Im theta_i¦ < s}, u : T_s -> H holomorphic, 1-periodic, ¦¦u¦¦ <= M on T_s (M >= 0); hat u_k = int_{[0,1]^n} u(x) e^{-2 pi i k.x} dx; (ii) c_k in H with sum ¦¦c_k¦¦ e^{2pi¦k¦_1 s} < infinity; local data: g continuous periodic H-valued with ¦¦g¦¦ <= M
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:fourier-l2 (for all such data); within the step: eta; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: sum_k ¦¦hat g_k¦¦^2 = int ¦¦g¦¦^2 <= M^2; hence sum_k ¦¦hat u_k¦¦^2 e^{-4 pi k.eta} <= M^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-fourier, bpW:w1:ext-series, stepW:w1:shift
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-fourier | blueprint-W/parts/w1-sequences.tex#stepW:w1:parseval@L978-L978 | scalar Parseval
EDGE: bpW:w1:ext-series | blueprint-W/parts/w1-sequences.tex#stepW:w1:parseval@L978-L978 | Tonelli over the orthonormal basis
EDGE: stepW:w1:shift | blueprint-W/parts/w1-sequences.tex#stepW:w1:parseval@L979-L979 | the shifted coefficients
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:orthants
KIND: step
TITLE: Orthants
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:orthants@L980-L983
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:orthants@L980-L983
CONTRACT_ID: stepW:w1:orthants
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:fourier-l2: H complex Hilbert space, n >= 1, s > 0, T_s = {max ¦Im theta_i¦ < s}, u : T_s -> H holomorphic, 1-periodic, ¦¦u¦¦ <= M on T_s (M >= 0); hat u_k = int_{[0,1]^n} u(x) e^{-2 pi i k.x} dx; (ii) c_k in H with sum ¦¦c_k¦¦ e^{2pi¦k¦_1 s} < infinity; local data: s' < s
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:fourier-l2 (for all such data); within the step: eps in {+-1}^n; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: e^{4 pi s' ¦k¦_1} <= sum_eps e^{4 pi s' eps.k}; summing the 2^n shifts eta = -s' eps gives (i) with s', and monotone convergence gives s
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:parseval
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:parseval | blueprint-W/parts/w1-sequences.tex#stepW:w1:orthants@L981-L981 | the bound for each eta
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:fsum
KIND: step
TITLE: Summation
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fsum@L984-L989
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fsum@L984-L989
CONTRACT_ID: stepW:w1:fsum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:fourier-l2: H complex Hilbert space, n >= 1, s > 0, T_s = {max ¦Im theta_i¦ < s}, u : T_s -> H holomorphic, 1-periodic, ¦¦u¦¦ <= M on T_s (M >= 0); hat u_k = int_{[0,1]^n} u(x) e^{-2 pi i k.x} dx; (ii) c_k in H with sum ¦¦c_k¦¦ e^{2pi¦k¦_1 s} < infinity; local data: (ii): sum ¦¦c_k¦¦ e^{2 pi ¦k¦_1 s} < infinity; (iii): u as in (i), s' < s
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:fourier-l2 (for all such data); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (ii) uniform convergence of holomorphic partial sums, holomorphy of the limit, coefficients termwise; (iii) sum ¦¦hat u_k¦¦ e^{2pi¦k¦_1 s'} <= 2^{n/2} M (sum e^{-4pi¦k¦_1(s-s')})^{1/2} < infinity, and the sum v of (ii) equals u on R^n (scalar uniqueness) and on T_{s'} (identity theorem)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:uniform-limit, bpW:w1:ext-integral, stepW:w1:orthants, K:bp:p1:fourier-basic, K:bp:p1:strip-identity
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:uniform-limit | blueprint-W/parts/w1-sequences.tex#stepW:w1:fsum@L986-L986 | holomorphy of the uniform limit
EDGE: bpW:w1:ext-integral | blueprint-W/parts/w1-sequences.tex#stepW:w1:fsum@L986-L986 | term-by-term integration of the coefficients
EDGE: stepW:w1:orthants | blueprint-W/parts/w1-sequences.tex#stepW:w1:fsum@L987-L987 | (i) in the Cauchy-Schwarz bound
EDGE: K:bp:p1:fourier-basic | blueprint-W/parts/w1-sequences.tex#stepW:w1:fsum@L989-L989 | (b): a continuous periodic function with vanishing coefficients is 0
EDGE: K:bp:p1:strip-identity | blueprint-W/parts/w1-sequences.tex#stepW:w1:fsum@L989-L989 | identity theorem on strips
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:fourier-banach
KIND: lemma
TITLE: Banach-valued Fourier coefficients on strips
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-banach@L996-L1012
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-banach@L1014-L1029
CONTRACT_ID: bpW:w1:fourier-banach
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: F complex Banach, n >= 1, s > 0, M >= 0, u : T_s -> F holomorphic, 1-periodic, ¦¦u¦¦ <= M on T_s; hat u_k (Bochner integral); (ii) 0 < sigma < s, c >= 0; (iii) c_k in F with sum ¦¦c_k¦¦ e^{2pi¦k¦_1 rho} < infinity for some rho > 0
SOURCE_QUANTIFIERS: for all such data; k in Z^n
SOURCE_CONCLUSION: (i) ¦¦hat u_k¦¦ <= M e^{-2 pi ¦k¦_1 s}; (ii) sum_k ¦¦hat u_k¦¦ e^{2pi¦k¦_1(s-sigma)} <= M coth(pi sigma)^n and sum_k (1+¦k¦_1)^c ¦¦hat u_k¦¦ e^{2pi¦k¦_1(s-sigma)} <= M S_{n,c}(sigma); (iii) v = sum c_k e^{2pi i k.theta} converges absolutely and uniformly on T_rho, is holomorphic and 1-periodic, hat v_k = c_k, ¦¦v¦¦ <= sum ¦¦c_k¦¦ e^{2pi¦k¦_1 rho}; (iv) everything is linear in u (parameter-difference versions)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:holomorphic, bpW:w1:lattice, stepW:w1:fbdual, stepW:w1:fbdecay, stepW:w1:fbsum, stepW:w1:fbconv
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:holomorphic | blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-banach@L999-L999 | holomorphic maps
EDGE: bpW:w1:lattice | blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-banach@L1005-L1005 | S_{n,c}
EDGE: stepW:w1:fbdual | blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-banach@L1015-L1015 | proof step
EDGE: stepW:w1:fbdecay | blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-banach@L1019-L1019 | proof step
EDGE: stepW:w1:fbsum | blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-banach@L1023-L1023 | proof step
EDGE: stepW:w1:fbconv | blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-banach@L1025-L1025 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:fbdual
KIND: step
TITLE: Scalar reduction
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fbdual@L1015-L1018
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fbdual@L1015-L1018
CONTRACT_ID: stepW:w1:fbdual
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:fourier-banach: F complex Banach, n >= 1, s > 0, M >= 0, u : T_s -> F holomorphic, 1-periodic, ¦¦u¦¦ <= M on T_s; hat u_k (Bochner integral); (ii) 0 < sigma < s, c >= 0; (iii) c_k in F with sum ¦¦c_k¦¦ e^{2pi¦k¦_1 rho} < infinity for some rho > 0; local data: phi in F*, ¦¦phi¦¦ <= 1
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:fourier-banach (for all such data; k in Z^n); within the step: phi; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: phi o u is holomorphic, 1-periodic, bounded by M, and phi(hat u_k) = (phi o u)^_k
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-onevar
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-onevar | blueprint-W/parts/w1-sequences.tex#stepW:w1:fbdual@L1018-L1018 | continuous linear maps commute with Bochner integrals
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:fbdecay
KIND: step
TITLE: Scalar decay
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fbdecay@L1019-L1022
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fbdecay@L1019-L1022
CONTRACT_ID: stepW:w1:fbdecay
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:fourier-banach: F complex Banach, n >= 1, s > 0, M >= 0, u : T_s -> F holomorphic, 1-periodic, ¦¦u¦¦ <= M on T_s; hat u_k (Bochner integral); (ii) 0 < sigma < s, c >= 0; (iii) c_k in F with sum ¦¦c_k¦¦ e^{2pi¦k¦_1 rho} < infinity for some rho > 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:fourier-banach (for all such data; k in Z^n); within the step: k; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦(phi o u)^_k¦ <= e^{-2pi¦k¦_1 s'} M for 0 <= s' < s; s' -> s; for all norm-one phi, ¦¦hat u_k¦¦ <= M e^{-2pi¦k¦_1 s}; this is (i)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:fbdual, K:bp:p1:decay, bpW:w1:ext-onevar
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:fbdual | blueprint-W/parts/w1-sequences.tex#stepW:w1:fbdecay@L1020-L1020 | the scalar functions phi o u
EDGE: K:bp:p1:decay | blueprint-W/parts/w1-sequences.tex#stepW:w1:fbdecay@L1020-L1020 | scalar coefficient decay
EDGE: bpW:w1:ext-onevar | blueprint-W/parts/w1-sequences.tex#stepW:w1:fbdecay@L1022-L1022 | the norm is attained by norm-one functionals
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:fbsum
KIND: step
TITLE: Lattice sum
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fbsum@L1023-L1024
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fbsum@L1023-L1024
CONTRACT_ID: stepW:w1:fbsum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:fourier-banach: F complex Banach, n >= 1, s > 0, M >= 0, u : T_s -> F holomorphic, 1-periodic, ¦¦u¦¦ <= M on T_s; hat u_k (Bochner integral); (ii) 0 < sigma < s, c >= 0; (iii) c_k in F with sum ¦¦c_k¦¦ e^{2pi¦k¦_1 rho} < infinity for some rho > 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:fourier-banach (for all such data; k in Z^n); within the step: sigma; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦¦hat u_k¦¦ e^{2pi¦k¦_1(s-sigma)} <= M e^{-2pi¦k¦_1 sigma}, summed with Lemma bpW:w1:lattice; this is (ii)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:fbdecay, bpW:w1:lattice
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:fbdecay | blueprint-W/parts/w1-sequences.tex#stepW:w1:fbsum@L1024-L1024 | (i)
EDGE: bpW:w1:lattice | blueprint-W/parts/w1-sequences.tex#stepW:w1:fbsum@L1024-L1024 | (i), (iii): the lattice sums
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:fbconv
KIND: step
TITLE: Summation
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fbconv@L1025-L1028
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fbconv@L1025-L1028
CONTRACT_ID: stepW:w1:fbconv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:fourier-banach: F complex Banach, n >= 1, s > 0, M >= 0, u : T_s -> F holomorphic, 1-periodic, ¦¦u¦¦ <= M on T_s; hat u_k (Bochner integral); (ii) 0 < sigma < s, c >= 0; (iii) c_k in F with sum ¦¦c_k¦¦ e^{2pi¦k¦_1 rho} < infinity for some rho > 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:fourier-banach (for all such data; k in Z^n); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the partial sums converge uniformly on T_rho; the limit is holomorphic; coefficients by term-by-term integration; (iv) by linearity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:uniform-limit, bpW:w1:ext-integral
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:uniform-limit | blueprint-W/parts/w1-sequences.tex#stepW:w1:fbconv@L1027-L1027 | (i): holomorphy of the uniform limit
EDGE: bpW:w1:ext-integral | blueprint-W/parts/w1-sequences.tex#stepW:w1:fbconv@L1028-L1028 | term-by-term integration
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:lattice
KIND: lemma
TITLE: Weighted lattice sums
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:lattice@L1033-L1047
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:lattice@L1049-L1065
CONTRACT_ID: bpW:w1:lattice
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n >= 1, sigma > 0, eps = 2 pi sigma, ¦k¦_1 = sum ¦k_i¦; (iii) c >= 0, b = c + n - 1; (iv) tau >= 1, gamma, beta >= 0
SOURCE_QUANTIFIERS: for all such data
SOURCE_CONCLUSION: (i) sum_k e^{-eps¦k¦_1} = coth(eps/2)^n = coth(pi sigma)^n; (ii) #{k : ¦k¦_1 = m} <= 2^n binom(m+n-1,n-1) <= 2^n (m+1)^{n-1}; (iii) sum_k (1+¦k¦_1)^c e^{-eps¦k¦_1} <= S_{n,c}(sigma) := 2^n (2b/(e eps))^b e^{eps/2} (1 + 2/eps) ((2b/(e eps))^b := 1 for b = 0); (iv) A_k = 1 + ¦k¦_1^tau <= (1+¦k¦_1)^tau, so sum A_k^gamma (1+¦k¦_1)^beta e^{-eps¦k¦_1} <= S_{n,gamma tau + beta}(sigma), and P96-K's B_sigma^2 <= 2^n S_{n,4tau+2}(sigma/pi) in period-one units
CONSTANT_SCOPE: S_{n,c}(sigma) explicit in n, c, sigma
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:latprod, stepW:w1:latcount, stepW:w1:latweight, stepW:w1:latdiv
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:latprod | blueprint-W/parts/w1-sequences.tex#bpW:w1:lattice@L1050-L1050 | proof step
EDGE: stepW:w1:latcount | blueprint-W/parts/w1-sequences.tex#bpW:w1:lattice@L1054-L1054 | proof step
EDGE: stepW:w1:latweight | blueprint-W/parts/w1-sequences.tex#bpW:w1:lattice@L1057-L1057 | proof step
EDGE: stepW:w1:latdiv | blueprint-W/parts/w1-sequences.tex#bpW:w1:lattice@L1062-L1062 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:latprod
KIND: step
TITLE: Product
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:latprod@L1050-L1053
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:latprod@L1050-L1053
CONTRACT_ID: stepW:w1:latprod
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:lattice: n >= 1, sigma > 0, eps = 2 pi sigma, ¦k¦_1 = sum ¦k_i¦; (iii) c >= 0, b = c + n - 1; (iv) tau >= 1, gamma, beta >= 0; local data: eps > 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:lattice (for all such data); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the sum factorizes and sum_{m in Z} e^{-eps¦m¦} = coth(eps/2)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-series
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-series | blueprint-W/parts/w1-sequences.tex#stepW:w1:latprod@L1052-L1052 | Tonelli for the product sum
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:latcount
KIND: step
TITLE: Counting
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:latcount@L1054-L1056
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:latcount@L1054-L1056
CONTRACT_ID: stepW:w1:latcount
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:lattice: n >= 1, sigma > 0, eps = 2 pi sigma, ¦k¦_1 = sum ¦k_i¦; (iii) c >= 0, b = c + n - 1; (iv) tau >= 1, gamma, beta >= 0; local data: m >= 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:lattice (for all such data); within the step: m; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: #{k : ¦k¦_1 = m} <= 2^n binom(m+n-1,n-1) <= 2^n (m+1)^{n-1}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:latweight
KIND: step
TITLE: Weighted sum
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:latweight@L1057-L1061
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:latweight@L1057-L1061
CONTRACT_ID: stepW:w1:latweight
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:lattice: n >= 1, sigma > 0, eps = 2 pi sigma, ¦k¦_1 = sum ¦k_i¦; (iii) c >= 0, b = c + n - 1; (iv) tau >= 1, gamma, beta >= 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:lattice (for all such data); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the sum in (iii) is at most 2^n sum_m (m+1)^b e^{-eps m} <= S_{n,c}(sigma), using t^b e^{-eps t/2} <= (2b/(e eps))^b and 1 - e^{-x} >= x/(1+x)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:latcount
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:latcount | blueprint-W/parts/w1-sequences.tex#stepW:w1:latweight@L1058-L1058 | (ii)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:latdiv
KIND: step
TITLE: Divisor weights
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:latdiv@L1062-L1064
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:latdiv@L1062-L1064
CONTRACT_ID: stepW:w1:latdiv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:lattice: n >= 1, sigma > 0, eps = 2 pi sigma, ¦k¦_1 = sum ¦k_i¦; (iii) c >= 0, b = c + n - 1; (iv) tau >= 1, gamma, beta >= 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:lattice (for all such data); within the step: x >= 0; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: 1 + x^tau <= (1+x)^tau; the B_sigma statement by the substitution ¦k¦ = ¦k¦_1, e^{-2¦k¦sigma_K} = e^{-2pi¦k¦_1(sigma_K/pi)}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:latweight
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:latweight | blueprint-W/parts/w1-sequences.tex#stepW:w1:latdiv@L1064-L1064 | (iii) with c = gamma tau + beta
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:schur
KIND: lemma
TITLE: Hilbert-matrix bound
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:schur@L1110-L1121
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:schur@L1123-L1138
CONTRACT_ID: bpW:w1:schur
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: A bounded on l^2_K with matrix A_ij = (A e_j)_i; (iii) F_ij with ¦F_ij¦ <= c¦A_ij¦/¦i-j¦ (i != j), ¦F_ii¦ <= c¦A_ii¦; (iv) A : l^{a,p}_K -> l^{a,bar p}_K via its representative
SOURCE_QUANTIFIERS: for all such A, F, c
SOURCE_CONCLUSION: (i) B_ij = ¦A_ij¦/¦i-j¦ (i != j), B_ii = 0 defines a bounded operator with absolutely convergent rows and ¦¦B¦¦ <= (pi/sqrt3)¦¦A¦¦; (ii) the diagonal (A_ii) is a multiplier with norm <= ¦¦A¦¦; (iii) ¦¦F¦¦ <= c(1 + pi/sqrt3)¦¦A¦¦ <= 3c¦¦A¦¦; (iv) the same for weighted spaces via the representative hat A (ratios unchanged by the weights)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:transport, stepW:w1:rows, stepW:w1:schurtest, stepW:w1:diagcomb, stepW:w1:schurweights
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:transport | blueprint-W/parts/w1-sequences.tex#bpW:w1:schur@L1119-L1119 | the representative hat A
EDGE: stepW:w1:rows | blueprint-W/parts/w1-sequences.tex#bpW:w1:schur@L1124-L1124 | proof step
EDGE: stepW:w1:schurtest | blueprint-W/parts/w1-sequences.tex#bpW:w1:schur@L1128-L1128 | proof step
EDGE: stepW:w1:diagcomb | blueprint-W/parts/w1-sequences.tex#bpW:w1:schur@L1131-L1131 | proof step
EDGE: stepW:w1:schurweights | blueprint-W/parts/w1-sequences.tex#bpW:w1:schur@L1136-L1136 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:rows
KIND: step
TITLE: Row and column sums
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:rows@L1124-L1127
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:rows@L1124-L1127
CONTRACT_ID: stepW:w1:rows
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:schur: A bounded on l^2_K with matrix A_ij = (A e_j)_i; (iii) F_ij with ¦F_ij¦ <= c¦A_ij¦/¦i-j¦ (i != j), ¦F_ii¦ <= c¦A_ii¦; (iv) A : l^{a,p}_K -> l^{a,bar p}_K via its representative
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:schur (for all such A, F, c); within the step: i, j; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: sum_j ¦A_ij¦^2 <= ¦¦A¦¦^2, sum_i ¦A_ij¦^2 <= ¦¦A¦¦^2; row and column sums of B at most (pi/sqrt3)¦¦A¦¦
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-series
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-series | blueprint-W/parts/w1-sequences.tex#stepW:w1:rows@L1126-L1126 | sum_{k != 0} k^{-2} = pi^2/3
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:schurtest
KIND: step
TITLE: Schur test
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:schurtest@L1128-L1130
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:schurtest@L1128-L1130
CONTRACT_ID: stepW:w1:schurtest
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:schur: A bounded on l^2_K with matrix A_ij = (A e_j)_i; (iii) F_ij with ¦F_ij¦ <= c¦A_ij¦/¦i-j¦ (i != j), ¦F_ii¦ <= c¦A_ii¦; (iv) A : l^{a,p}_K -> l^{a,bar p}_K via its representative
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:schur (for all such A, F, c); within the step: v; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦¦Bv¦¦^2 <= Lambda^2 ¦¦A¦¦^2 ¦¦v¦¦^2 (Schur test)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:rows, bpW:w1:ext-lp
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:rows | blueprint-W/parts/w1-sequences.tex#stepW:w1:schurtest@L1129-L1129 | row and column sums
EDGE: bpW:w1:ext-lp | blueprint-W/parts/w1-sequences.tex#stepW:w1:schurtest@L1130-L1130 | norm bounds via finite partial sums
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:diagcomb
KIND: step
TITLE: Diagonal and combination
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:diagcomb@L1131-L1135
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:diagcomb@L1131-L1135
CONTRACT_ID: stepW:w1:diagcomb
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:schur: A bounded on l^2_K with matrix A_ij = (A e_j)_i; (iii) F_ij with ¦F_ij¦ <= c¦A_ij¦/¦i-j¦ (i != j), ¦F_ii¦ <= c¦A_ii¦; (iv) A : l^{a,p}_K -> l^{a,bar p}_K via its representative
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:schur (for all such A, F, c); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦A_ii¦ <= ¦¦A¦¦; the diagonal is a multiplier; F is dominated entrywise by cB + c diag(¦A_ii¦), so ¦¦F¦¦ <= c(1 + pi/sqrt3)¦¦A¦¦ < 3c¦¦A¦¦
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:multiplier, stepW:w1:schurtest
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:multiplier | blueprint-W/parts/w1-sequences.tex#stepW:w1:diagcomb@L1132-L1132 | diagonal multipliers
EDGE: stepW:w1:schurtest | blueprint-W/parts/w1-sequences.tex#stepW:w1:diagcomb@L1133-L1133 | the bound on B
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:schurweights
KIND: step
TITLE: Weights
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:schurweights@L1136-L1137
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:schurweights@L1136-L1137
CONTRACT_ID: stepW:w1:schurweights
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:schur: A bounded on l^2_K with matrix A_ij = (A e_j)_i; (iii) F_ij with ¦F_ij¦ <= c¦A_ij¦/¦i-j¦ (i != j), ¦F_ii¦ <= c¦A_ii¦; (iv) A : l^{a,p}_K -> l^{a,bar p}_K via its representative; local data: A : l^{a,p} -> l^{a,bar p}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:schur (for all such A, F, c); within the step: i, j; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: hat A_ij = omega_{a,bar p}(i) A_ij/omega_{a,p}(j), likewise for F, so the hypotheses of (iii) transfer
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:transport
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:transport | blueprint-W/parts/w1-sequences.tex#stepW:w1:schurweights@L1137-L1137 | the representative
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
